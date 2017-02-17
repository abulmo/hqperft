/*
 * hqperft.c
 *
 * perft using Hyperbola quintessence & range attacks
 *
 * © 2017 Richard Delorme
 * version 1.0
 */

/* Includes */
#include <ctype.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#ifndef _ISOC11_SOURCE
void* aligned_alloc(size_t, size_t);
#endif

#if defined(__unix__) || defined(__APPLE__)
#include <unistd.h>
#include <sys/time.h>
#endif

#ifdef _WIN32
#include <windows.h>
#include <malloc.h>
#define aligned_alloc _aligned_malloc
#endif

/* Types */
typedef enum {GAME_SIZE = 4096, MOVE_SIZE = 256} Limits;

typedef uint64_t Bitboard;

typedef uint64_t Random;

typedef enum { WHITE, BLACK, COLOR_SIZE } Color;

typedef enum
{
	A1, B1, C1, D1, E1, F1, G1, H1,
	A2, B2, C2, D2, E2, F2, G2, H2,
	A3, B3, C3, D3, E3, F3, G3, H3,
	A4, B4, C4, D4, E4, F4, G4, H4,
	A5, B5, C5, D5, E5, F5, G5, H5,
	A6, B6, C6, D6, E6, F6, G6, H6,
	A7, B7, C7, D7, E7, F7, G7, H7,
	A8, B8, C8, D8, E8, F8, G8, H8,
	BOARD_SIZE, ENPASSANT_NONE = BOARD_SIZE, OUT = -1
} Square;

typedef enum { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PIECE_SIZE } Piece;

typedef enum { EMPTY, WPAWN, BPAWN, WKNIGHT, BKNIGHT, WBISHOP, BBISHOP, WROOK, BROOK, WQUEEN, BQUEEN, WKING, BKING, CPIECE_SIZE } CPiece;

typedef enum { KNIGHT_PROMOTION = 0x1000, BISHOP_PROMOTION = 0x2000, ROOK_PROMOTION = 0x3000, QUEEN_PROMOTION = 0x4000 } Promotion;

typedef uint16_t Move;

typedef struct Key {
	uint64_t code;
	uint32_t index;
} Key;

typedef struct Mask {
	Bitboard bit;
	Bitboard diagonal;
	Bitboard antidiagonal;
	Bitboard vertical;
	Bitboard pawn_attack[COLOR_SIZE];
	Bitboard pawn_push[COLOR_SIZE];
	Bitboard enpassant;
	Bitboard knight;
	Bitboard king;
} Mask;

typedef struct BoardStack {
	Bitboard pinned;
	Bitboard checkers;
	Key key;
	uint8_t castling;
	uint8_t enpassant;
	uint8_t victim;
	uint8_t padding;
} BoardStack;

typedef struct Board {
	Bitboard piece[PIECE_SIZE];
	Bitboard color[COLOR_SIZE];
	uint8_t cpiece[BOARD_SIZE];
	BoardStack stack_[GAME_SIZE],*stack;
	Square x_king[COLOR_SIZE];
	int ply;
	Color player;
} Board;

typedef struct MoveArray {
	Move move[MOVE_SIZE];
	int n;
	int i;
} MoveArray;

typedef struct {
	uint64_t code;
	uint64_t count;
	int depth;
} Hash;

typedef struct {
	Hash *hash;
	uint64_t mask;
} HashTable;

/* Constants */
#define FILE_A 0x0101010101010101ULL
#define FILE_H 0x8080808080808080ULL
#define RANK_1 0x00000000000000ffULL
#define RANK_2 0x000000000000ff00ULL
#define RANK_3 0x0000000000ff0000ULL
#define RANK_6 0x0000ff0000000000ULL
#define RANK_7 0x00ff000000000000ULL
#define RANK_8 0xff00000000000000ULL
const int PUSH[] = {8, -8};
const uint8_t MASK_CASTLING[BOARD_SIZE] = {
	13,15,15,15,12,15,15,14,
	15,15,15,15,15,15,15,15,
	15,15,15,15,15,15,15,15,
	15,15,15,15,15,15,15,15,
	15,15,15,15,15,15,15,15,
	15,15,15,15,15,15,15,15,
	15,15,15,15,15,15,15,15,
	 7,15,15,15, 3,15,15,11
};
const int CAN_CASTLE_KINGSIDE[COLOR_SIZE] = {1, 4};
const int CAN_CASTLE_QUEENSIDE[COLOR_SIZE] = {2, 8};
const Bitboard PROMOTION_RANK[] = {RANK_8, RANK_1};
const Random MASK48 = 0xFFFFFFFFFFFFull;
const int BUCKET_SIZE = 4;

/* Globals */
Mask MASK[BOARD_SIZE];
uint8_t RANK_ATTACK[512];
Bitboard BETWEEN[BOARD_SIZE][BOARD_SIZE];
int DIRECTION[BOARD_SIZE][BOARD_SIZE];
Key KEY_PLAYER[COLOR_SIZE];
Key KEY_SQUARE[BOARD_SIZE][CPIECE_SIZE];
Key KEY_CASTLING[16];
Key KEY_ENPASSANT[BOARD_SIZE + 1];
Key KEY_PLAY;


/* Count moves from a bitboard */
int count_moves(Bitboard b) {
#if defined(POPCOUNT) && defined(USE_MSVC_X64)
		return __popcnt64(b);
#elif defined(POPCOUNT) && defined(USE_GCC_X64)
		return __builtin_popcountll(b);
#else
	Bitboard c = b
		- ((b >> 1) & 0x7777777777777777ULL)
		- ((b >> 2) & 0x3333333333333333ULL)
		- ((b >> 3) & 0x1111111111111111ULL);
	c = ((c + (c >> 4)) & 0x0F0F0F0F0F0F0F0FULL) * 0x0101010101010101ULL;

	return  (int)(c >> 56);
#endif
}

/* Verify if only one bit is set. */
bool is_single(Bitboard b) {
	return (b & (b - 1)) == 0;
}

/* Byte swap (= vertical mirror) */
Bitboard bit_bswap(Bitboard b) {
#if defined(USE_MSVC_X64)
	return _byteswap_uint64(b);
#elif defined(USE_GCC_X64)
	return __builtin_bswap64(b);
#else
	b = ((b >>  8) & 0x00FF00FF00FF00FFULL) | ((b <<  8) & 0xFF00FF00FF00FF00ULL);
	b = ((b >> 16) & 0x0000FFFF0000FFFFULL) | ((b << 16) & 0xFFFF0000FFFF0000ULL);
	b = ((b >> 32) & 0x00000000FFFFFFFFULL) | ((b << 32) & 0xFFFFFFFF00000000ULL);
	return b;
#endif
}

/* Create a bitboard with one bit set*/
Bitboard x_to_bit(const int x) {
	return 1ULL << x;
}

/* Time in seconds */
double chrono(void) {
	#if defined(__unix__) || defined(__APPLE__)
		#if _POSIX_TIMERS > 0
			struct timespec t;
			clock_gettime(CLOCK_MONOTONIC, &t);
			return 0.000000001 * t.tv_nsec + t.tv_sec;
		#else
			struct timeval t;
			gettimeofday(&t, NULL);
			return 0.000001 * t.tv_usec + t.tv_sec;
		#endif
	#elif defined(_WIN32)
		return 0.001 * GetTickCount();
	#endif
}

/* Memory error */
void memory_error(const char *function) {
	fprintf(stderr, "Fatal Error: memory allocation failure in %s\n", function);
	exit(EXIT_FAILURE);
}

/* Parse error. */
void parse_error(const char *string, const char *done, const char *msg) {
	int n;

	fprintf(stderr, "\nError in %s '%s'\n", msg, string);
	n = 9 + strlen(msg) + done - string;	if (n > 0 && n < 256) {
		while (n--) putc('-', stderr);
		putc('^', stderr); putc('\n', stderr); putc('\n', stderr);
	}
	exit(EXIT_FAILURE);
}

/* Skip spaces */
char *parse_next(const char *s) {
	while (isspace(*s)) ++s;
	return (char*) s;
}

/* Get a random number */
uint64_t random_get(Random *random) {
	const uint64_t A = 0x5DEECE66Dull;
	const uint64_t B = 0xBull;
	register uint64_t r;

	*random = ((A * *random + B) & MASK48);
	r = *random >> 16;
	*random = ((A * *random + B) & MASK48);
	return (r << 32) | (*random >> 16);
}

/* Init the random generator */
void random_seed(Random *random, const uint64_t seed) {
	*random = (seed & MASK48);
}

/* Opponent color */
Color opponent(const Color c) {
	return !c;
}

/* Convert a char to a Color */
Color color_from_char(const char c) {
	switch (tolower(c)) {
		case 'b': return BLACK;
		case 'w': return WHITE;
		default: return COLOR_SIZE;
	}
}

/* Loop over each color */
#define foreach_color(c) for ((c) = WHITE; (c) < COLOR_SIZE; ++(c))

/* Make a square from file & rank */
Square square(const int f, const int r) {
	return (r << 3) + f;
}

/* Get square rank */
Square rank(const Square x) {
	return x >> 3;
}

/* Get square file */
Square file(const Square x) {
	return x & 7;
}

/* Parse a square from a string. */
bool square_parse(char **string, Square *x) {
	const char *s = *string;
	if ('a' <= s[0] && s[0] <= 'h' && '1' <= s[1] && s[1] <= '8') {
		*x = square(s[0] - 'a', s[1] - '1');
		*string += 2;
		return true;
	} else return false;
}

/* Get the first occupied square from a bitboard */
Square square_first(Bitboard b) {
#if defined(USE_MSVC_X64)
	unsigned long index;
	_BitScanForward64(&index, b);
	return (int) index;
#elif defined(USE_GCC_X64)
	return __builtin_ctzll(b);
#else
	const int magic[64] = {
		63,  0, 58,  1, 59, 47, 53,  2,
		60, 39, 48, 27, 54, 33, 42,  3,
		61, 51, 37, 40, 49, 18, 28, 20,
		55, 30, 34, 11, 43, 14, 22,  4,
		62, 57, 46, 52, 38, 26, 32, 41,
		50, 36, 17, 19, 29, 10, 13, 21,
		56, 45, 25, 31, 35, 16,  9, 12,
		44, 24, 15,  8, 23,  7,  6,  5
	};
	return magic[((b & (-b)) * 0x07EDD5E59A4E28C2ULL) >> 58];
#endif
}

/* Get the next occupied square from a bitboard */
Square square_next(Bitboard *b) {
	int i = square_first(*b);
	*b &= *b - 1;
	return i;
}

/* Loop over each square */
#define foreach_square(x) for ((x) = A1; (x) < BOARD_SIZE; ++(x))

/* Check if square 'x' is on 7th rank */
bool is_on_seventh_rank(const Square x, const Color c) {
	return c ? rank(x) == 1 : rank(x) == 6;
}

/* Check if square 'x' is on 2nd rank */
bool is_on_second_rank(const Square x, const Color c) {
	return c ? rank(x) == 6 : rank(x) == 1;
}

/* Convert a char to a piece */
Piece piece_from_char(const char c) {
	Piece p;

	for (p = PAWN; p < PIECE_SIZE; ++p) if ("pnbrqk"[p] == tolower(c)) break;
	return p;
}

/* Loop over each cpiece */
#define foreach_cpiece(cp) for ((cp) = WPAWN; (cp) < CPIECE_SIZE; ++(cp))

/* make a colored piece */
CPiece cpiece_make(Piece p, const Color c) {
	return (p << 1) + c + 1;
}

/* Get the Piece of a CPiece*/
Piece cpiece_piece(CPiece p) {
	return (p - 1) >> 1;
}

/* Get the color of a CPiece */
Color cpiece_color(CPiece p) {
	return (p - 1) & 1;
}

/* Convert a char to a colored piece */
CPiece cpiece_from_char(const char c) {
	CPiece p;

	foreach_cpiece(p) if ("#PpNnBbRrQqKk"[p] == c) break;
	return p;
}

/* Convert a char to a castling flag */
int castling_from_char(const char c) {
	switch (c) {
		case 'K': return 1;
		case 'Q': return 2;
		case 'k': return 4;
		case 'q': return 8;
		default: return 0;
	}
}

/* Get the origin square of a move */
Square move_from(const Move move) {
	return move & 63;
}

/* Get the destination square of a move */
Square move_to(const Move move) {
	return (move >> 6) & 63;
}

/* Get the promoted piece of a move */
Piece move_promotion(const Move move) {
	return move >> 12;
}

/* Convert a move to a string */
char* move_to_string(const Move move, char *s) {
	static char string[8];

	if (s == NULL) s = string;
	if (move) {
		s[0] = (move & 7) + 'a';
		s[1] = (move >> 3 & 7) + '1';
		s[2] = (move >> 6 & 7) + 'a';
		s[3] = (move >> 9 & 7) + '1';
		s[4] = "\0NBRQ"[move_promotion(move)];
		s[5] = '\0';
	} else {
		strcpy(s, "null");
	}

	return s;
}

/* Generate rank attack to fill the RANK_ATTACK array. */
int generate_rank_attack(int o, int  f) {
	int x, y;
	int b;

	y = 0;
	for (x = f - 1; x >= 0; --x) {
		b = 1 << x;
		y |= b;
		if ((o & b) == b) break;
	}
	for (x = f + 1; x < 8; ++x) {
		b = 1 << x;
		y |= b;
		if ((o & b) == b) break;
	}
	return y;
}

/* Generate attack using the hyperbola quintessence approach */
Bitboard attack(const Bitboard pieces, const Square x, const Bitboard mask) {
	Bitboard o = pieces & mask;
	Bitboard r = bit_bswap(o);

	return ((o - x_to_bit(x)) ^ bit_bswap(r - x_to_bit(x ^ 56))) & mask;
}

/* Generate attack for ranks. */
Bitboard rank_attack(const Bitboard pieces, const Square x) {
	Square file_mask = x & 7;
	Square rank_mask = x & 56;
	Bitboard o = (pieces >> rank_mask) & 126;

	return ((Bitboard) RANK_ATTACK[o * 4  + file_mask]) << rank_mask;
}

/* Generate attack for files. */
Bitboard vertical_attack(const Bitboard pieces, const Square x) {
	return attack(pieces, x, MASK[x].vertical);
}

/* Generate diagonal attack */
Bitboard diagonal_attack(const Bitboard pieces, const Square x) {
	return attack(pieces, x, MASK[x].diagonal);
}

/* Generate antidiagonal attack */
Bitboard antidiagonal_attack(const Bitboard pieces, const Square x) {
	return attack(pieces, x, MASK[x].antidiagonal);
}

/* Generate pawn attack (capture) */
Bitboard pawn_attack(const Square x, const Color c, const Bitboard target) {
	return MASK[x].pawn_attack[c] & target;
}

/* Generate knight attack */
Bitboard knight_attack(const Square x, const Bitboard target) {
	return MASK[x].knight & target;
}

/* Generate bishop attack */
Bitboard bishop_attack(const Bitboard pieces, const Square x, const Bitboard target) {
	return (diagonal_attack(pieces, x) + antidiagonal_attack(pieces, x)) & target;
}

/* Generate rook attack */
Bitboard rook_attack(const Bitboard pieces, const Square x, const Bitboard target) {
	return (vertical_attack(pieces, x) + rank_attack(pieces, x)) & target;
}

/* Generate king attack */
Bitboard king_attack(const Square x, const Bitboard target) {
	return MASK[x].king & target;
}

/* Init key to a random value */
void key_init(Key *key, Random *r) {
	key->code = random_get(r);
	key->index = (uint32_t) random_get(r);
}

/* Xor a key with another one */
void key_xor(Key *key, const Key *k) {
	key->code ^= k->code;
	key->index ^= k->index;
}

/* Set a key from a board */
void key_set(Key *key, const Board *board) {
	int x;

	*key = KEY_PLAYER[board->player];
	foreach_square (x) {
		key_xor(key, &KEY_SQUARE[x][board->cpiece[x]]);
	}
	key_xor(key, &KEY_CASTLING[board->stack->castling]);
	key_xor(key, &KEY_ENPASSANT[board->stack->enpassant]);
}

/* Update the key after a move is made */
void key_update(Key *key, const Board *board, const Move move) {
	const Square from = move_from(move);
	const Square to = move_to(move);
	CPiece cp = board->cpiece[from];
	Piece p = cpiece_piece(cp);
	const Color c = cpiece_color(cp);
	const CPiece victim = board->cpiece[to];
	const BoardStack *stack = board->stack;
	Square x, enpassant = ENPASSANT_NONE;

	*key = stack->key;

	// move the piece
	key_xor(key, &KEY_SQUARE[from][cp]);
	key_xor(key, &KEY_SQUARE[to][cp]);
	// capture
	if (victim) key_xor(key, &KEY_SQUARE[to][victim]);
	// pawn move
	if (p == PAWN) {
		if ((p = move_promotion(move))) {
			key_xor(key, &KEY_SQUARE[to][cp]);
			key_xor(key, &KEY_SQUARE[to][cpiece_make(p, c)]);
		} else if (stack->enpassant == to) {
			x = square(file(to), rank(from));
			key_xor(key, &KEY_SQUARE[x][cpiece_make(PAWN, opponent(c))]);
		} else if (abs(to - from) == 16 && (MASK[to].enpassant & (board->color[opponent(c)] & board->piece[PAWN]))) enpassant = (from + to) / 2;
	// castling
	} else if (p == KING) {
		if (to == from + 2) {
			cp = board->cpiece[from + 3];
			key_xor(key, &KEY_SQUARE[from + 3][cp]);
			key_xor(key, &KEY_SQUARE[from + 1][cp]);
		} else if (to == from - 2) {
			cp = board->cpiece[from - 4];
			key_xor(key, &KEY_SQUARE[from - 4][cp]);
			key_xor(key, &KEY_SQUARE[from - 1][cp]);
		}
	}
	// miscellaneous
	key_xor(key, &KEY_CASTLING[stack->castling]);
	key_xor(key, &KEY_CASTLING[stack->castling & MASK_CASTLING[from] & MASK_CASTLING[to]]);
	key_xor(key, &KEY_ENPASSANT[stack->enpassant]);
	key_xor(key, &KEY_ENPASSANT[enpassant]);
	key_xor(key, &KEY_PLAY);
}

/* Initialize some global constants */
void init(void) {
	int r, f, i, j, c;
	int x, y, z;
	static int d[64][64];
	Mask *mask;
	Random random[1];
	CPiece p;

	for (x = 0; x < 64; ++x) {
		for (y = 0; y < 64; ++y) d[x][y] = 0;
		// directions
		for (i = -1; i <= 1; ++i)
		for (j = -1; j <= 1; ++j) {
			if (i == 0 && j == 0) continue;
			f = x & 07;
			r = x >> 3;
			for (r += i, f += j; 0 <= r && r < 8 && 0 <= f && f < 8; r += i, f += j) {
		 		y = 8 * r + f;
				d[x][y] = 8 * i + j;
				DIRECTION[x][y] = abs(d[x][y]);
		 	}
		}
		// between
		for (y = 0; y < 64; ++y) {
			BETWEEN[x][y] = 0;
			i = d[x][y];
			if (i) {
				for (z = x + i; z != y; z += i) BETWEEN[x][y] |= x_to_bit(z);
			}
		}

		for (f = 0; f < 8; ++f) {
			RANK_ATTACK[x * 8 + f] = generate_rank_attack(x * 2, f);
		}
		// bitboard mask
		mask = MASK + x;
		mask->bit = 1ULL << x;
		mask->diagonal = 0;
		for (y = x - 9; y >= 0 && d[x][y] == -9; y -= 9) mask->diagonal |= x_to_bit(y);
		for (y = x + 9; y < 64 && d[x][y] == 9; y += 9) mask->diagonal |= x_to_bit(y);
		mask->antidiagonal = 0;
		for (y = x - 7; y >= 0 && d[x][y] == -7; y -= 7) mask->antidiagonal |= x_to_bit(y);
		for (y = x + 7; y < 64 && d[x][y] == 7; y += 7) mask->antidiagonal |= x_to_bit(y);
		mask->vertical = 0;
		for (y = x - 8; y >= 0; y -= 8) mask->vertical |= x_to_bit(y);
		for (y = x + 8; y < 64; y += 8) mask->vertical |= x_to_bit(y);

		f = x & 07;
		r = x >> 3;
		for (i = -1, c = 1; i <= 1; i += 2, c = 0) {
			mask->pawn_attack[c] = 0;
			for (j = -1; j <= 1; j += 2) {
				if (0 <= r + i && r + i < 8 && 0 <= f + j && f + j < 8) {
					 y = (r + i) * 8 + (f + j);
					 mask->pawn_attack[c] |= x_to_bit(y);
				}
			}
			if (0 <= r + i && r + i < 8) {
				y = (r + i) * 8 + f;
				mask->pawn_push[c] = x_to_bit(y);
			}
		}
		mask->enpassant = 0;
		if (r == 3 || r == 4) {
			if (f > 0) mask->enpassant |= x_to_bit(x - 1);
			if (f < 7) mask->enpassant |= x_to_bit(x + 1);
		}
		mask->knight = 0;
		for (i = -2; i <= 2; i = (i == -1 ? 1 : i + 1))
		for (j = -2; j <= 2; ++j) {
			if (i == j || i == -j || j == 0) continue;
			if (0 <= r + i && r + i < 8 && 0 <= f + j && f + j < 8) {
		 		y = 8 * (r + i) + (f + j);
		 		mask->knight |= x_to_bit(y);
			}
		}
		mask->king = 0;
		for (i = -1; i <= 1; ++i)
		for (j = -1; j <= 1; ++j) {
			if (i == 0 && j == 0) continue;
			if (0 <= r + i && r + i < 8 && 0 <= f + j && f + j < 8) {
		 		y = 8 * (r + i) + (f + j);
		 		mask->king |= x_to_bit(y);
			}
		}
	}

	// Hash key
	random_seed(random, 0xA170EBA);

	foreach_color (c) key_init(KEY_PLAYER + c, random);

	KEY_PLAY = KEY_PLAYER[WHITE];
	key_xor(&KEY_PLAY, &KEY_PLAYER[BLACK]);

	foreach_square (x)
	foreach_cpiece (p)
		key_init(&KEY_SQUARE[x][p], random);

	for (c = 1; c < 16; ++c) key_init(KEY_CASTLING + c, random);

	foreach_square (x) key_init(KEY_ENPASSANT + x, random);
	key_init(KEY_ENPASSANT + BOARD_SIZE, random);
}

/* check if an enpassant move is possible */
bool board_enpassant(const Board *board) {
	return board->stack->enpassant != ENPASSANT_NONE;
}

/* deplace a piece on the board */
void board_deplace_piece(Board *board, const Square from, const Square to) {
	const Bitboard b = x_to_bit(from) ^ x_to_bit(to);
	const CPiece cp = board->cpiece[from];
	const Piece p = cpiece_piece(cp);
	const Color c = cpiece_color(cp);

	board->piece[p] ^= b;
	board->color[c] ^= b;
	board->cpiece[to] = cp;
	board->cpiece[from] = EMPTY;
}

/* generate checker & pinned pieces */
void generate_checkers(Board *board) {
	const Color c = board->player;
	const Color o = opponent(c);
	const Square k = board->x_king[c];
	const Bitboard bq = (board->piece[BISHOP] + board->piece[QUEEN]) & board->color[o];
	const Bitboard rq = (board->piece[ROOK] + board->piece[QUEEN]) & board->color[o];
	const Bitboard pieces = board->color[WHITE] + board->color[BLACK];
	Bitboard partial_checkers;
	Bitboard b;
	Bitboard *pinned = &board->stack->pinned;
	Bitboard *checkers = &board->stack->checkers;
	Square x;

	*pinned = 0;

	// bishop or queen: all square reachable from the king square.
	b = diagonal_attack(pieces, k) + antidiagonal_attack(pieces, k);

	//checkers
	*checkers = partial_checkers = b & bq;

	// pinned square
	b &= board->color[c];
	if (b) {
		b = (diagonal_attack(pieces ^ b, k) + antidiagonal_attack(pieces ^ b, k)) & (bq ^ partial_checkers);
		while (b) {
			x = square_next(&b);
			*pinned |= BETWEEN[x][k] & board->color[c];
		}
	}

	// rook or queen: all square reachable from the king square.
	b = vertical_attack(pieces, k) + rank_attack(pieces, k);

	// checkers = opponent rook or queen
	*checkers |= partial_checkers = b & rq;

	// pinned square
	b &= board->color[c];
	if (b) {
		b = (vertical_attack(pieces ^ b, k) + rank_attack(pieces ^ b, k)) & (rq ^ partial_checkers);
		while (b) {
			x = square_next(&b);
			*pinned |= BETWEEN[x][k] & board->color[c];
		}
	}

	// other pieces (no more pins)
	*checkers |= knight_attack(k, board->piece[KNIGHT]);
	*checkers |= pawn_attack(k, c, board->piece[PAWN]);
	*checkers &= board->color[o];

	return;
}

/* Clear the board. Set all of its content to zeroes. */
void board_clear(Board *board) {
	memset(board, 0, sizeof (Board));
	board->stack = board->stack_;
}

/* Initialize the board to the starting position. */
void board_init(Board *board) {
	static const uint8_t cpiece[BOARD_SIZE] = {
		WROOK, WKNIGHT, WBISHOP, WQUEEN, WKING, WBISHOP, WKNIGHT, WROOK,
		WPAWN,WPAWN,WPAWN,WPAWN,WPAWN,WPAWN,WPAWN,WPAWN,
		EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,
		EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,
		EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,
		EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,EMPTY,
		BPAWN,BPAWN,BPAWN,BPAWN,BPAWN,BPAWN,BPAWN,BPAWN,
		BROOK, BKNIGHT, BBISHOP, BQUEEN, BKING, BBISHOP, BKNIGHT, BROOK
	};

	board_clear(board);
	memcpy(board->cpiece, cpiece, BOARD_SIZE);
	board->piece[PAWN] =   0x00ff00000000ff00ull;
	board->piece[KNIGHT] = 0x4200000000000042ull;
	board->piece[BISHOP] = 0x2400000000000024ull;
	board->piece[ROOK] =   0x8100000000000081ull;
	board->piece[QUEEN] =  0x0800000000000008ull;
	board->piece[KING] =   0x1000000000000010ull;
	board->color[WHITE] =  0x000000000000ffffull;
	board->color[BLACK] =  0xffff000000000000ull;
	board->stack->pinned = board->stack->checkers = 0;
	board->stack->castling = 15;
	board->stack->enpassant = ENPASSANT_NONE; // illegal enpassant square
	board->x_king[WHITE] = E1;
	board->x_king[BLACK] = E8;
	board->ply = 1;
	board->player = WHITE;

	key_set(&board->stack->key, board);
}

/* parse a FEN board description */
void board_set(Board *board, char *string) {
	char *s = string;
	Square x;
	int r, f;
	CPiece p;

	if (!s || *s == '\0') return;
	board_clear(board);
	// board
	r = 7, f = 0;
	do {
		if (*s == '/') {
			if (r <= 0) parse_error(string, s, "parse_fen: too many ranks");
			if (f != 8) parse_error(string, s, "parse_fen: missing square");
			f = 0; r--;
		} else if (isdigit(*s)) {
			f += (Square) (*s - '0');
			if (f > 8) parse_error(string, s, "parse_fen: file overflow");
		} else {
			if (f > 8) parse_error(string, s, "parse_fen: file overflow");
			x = square(f, r);
			board->cpiece[x] = p = cpiece_from_char(*s);
			if (board->cpiece[x] == CPIECE_SIZE) parse_error(string, s, "parse_fen: bad piece");
			board->piece[cpiece_piece(p)] |= x_to_bit(x);
			board->color[cpiece_color(p)] |= x_to_bit(x);
			if (cpiece_piece(p) == KING) board->x_king[cpiece_color(p)] = x;
			f++;
		}
		++s;
	} while (*s && *s != ' ');
	if (r < 0 || f != 8) parse_error(string, s, "parse_fen: missing square");
	// turn
	if (*s++ != ' ') parse_error(string, s, "parse_fen: missing space before player's turn");
	board->player = (uint8_t) color_from_char(*s);
	if (board->player == COLOR_SIZE) parse_error(string, s, "parse_fen: bad player's turn");
	++s;
	// castling
	s = parse_next(s);
	if (*s == '-') s++;
	else {
		while (*s && *s != ' ') {
			board->stack->castling |= castling_from_char(*s);
			s++;
		}
	}
	// correct castling
	if (board->cpiece[E1] == WKING) {
		if (board->cpiece[H1] != WROOK) board->stack->castling &= ~1;
		if (board->cpiece[A1] != WROOK) board->stack->castling &= ~2;
	} else board->stack->castling &= ~3;
	if (board->cpiece[E8] == BKING) {
		if (board->cpiece[H8] != BROOK) board->stack->castling &= ~4;
		if (board->cpiece[A8] != BROOK) board->stack->castling &= ~8;
	} else board->stack->castling &= ~12;
	// en passant
	x = 64;
	s = parse_next(s);
	if (*s == '-') s++;
	else if (!square_parse(&s, &x)) parse_error(string, s, "parse_fen: bad enpassant square");
	board->stack->enpassant = x;
	// update other chess board structure
	key_set(&board->stack->key, board);
	generate_checkers(board);
}

/* Create a board structure */
Board* board_create(void) {
	Board *board = malloc(sizeof (Board));
	if (board == NULL) memory_error(__func__);
	board_init(board);
	return board;
}

/* Destroy a board structure */
void board_destroy(Board* board) {
	free(board);
}

/* Play a move on the board. */
void board_update(Board *board, const Move move) {
	const Square from = move_from(move);
	const Square to = move_to(move);
	CPiece cp = board->cpiece[from];
	Piece p = cpiece_piece(cp);
	const Color c = cpiece_color(cp);
	const Bitboard b_from = x_to_bit(from);
	const Bitboard b_to = x_to_bit(to);
	const CPiece victim = board->cpiece[to];
	const BoardStack *current = board->stack;
	BoardStack *next = board->stack + 1;
	Square x;
	Bitboard b;

	// update chess board informations
	key_update(&next->key, board, move);
	next->castling = current->castling;
	next->enpassant = 64;
	next->victim = 0;
	next->castling &= MASK_CASTLING[from] & MASK_CASTLING[to];
	// move the piece
	board->piece[p] ^= b_from;
	board->piece[p] ^= b_to;
	board->color[c] ^= b_from | b_to;
	board->cpiece[from] = EMPTY;
	board->cpiece[to] = cp;
	// capture
	if (victim) {
		board->piece[cpiece_piece(victim)] ^= b_to;
		board->color[cpiece_color(victim)] ^= b_to;
		next->victim = victim;
	}
	// special pawn move
	if (p == PAWN) {
		if ((p = move_promotion(move))) {
			cp = cpiece_make(p, c);
			board->piece[PAWN] ^= b_to;
			board->piece[p] ^= b_to;
			board->cpiece[to] = cp;
		} else if (current->enpassant == to) {
			x = square(file(to), rank(from));
			b = x_to_bit(x);
			board->piece[PAWN] ^= b;
			board->color[opponent(c)] ^= b;
			board->cpiece[x] = EMPTY;
		} else if (abs(to - from) == 16 && (MASK[to].enpassant & (board->color[opponent(c)] & board->piece[PAWN]))) {
			next->enpassant = (from + to) / 2;
		}
	// king move
	} else if (p == KING) {
		board->x_king[c] = to;
		if (to == from + 2) board_deplace_piece(board, from + 3, from + 1);
		else if (to == from - 2) board_deplace_piece(board, from - 4, from - 1);
	}

	++board->stack;
	++board->ply;
	board->player = opponent(board->player);

	generate_checkers(board);
}

/* Undo a move from the board.*/
void board_restore(Board *board, const Move move) {
	const Square from = move_from(move);
	const Square to = move_to(move);
	CPiece cp = board->cpiece[to];
	Piece p = cpiece_piece(cp);
	const Color c = cpiece_color(cp);
	const Bitboard b_from = x_to_bit(from);
	const Bitboard b_to = x_to_bit(to);
	const CPiece victim = board->stack->victim;

	// miscellaneous
	--board->stack;
	--board->ply;
	board->player = opponent(board->player);

	// move the piece (with promotion)
	board->piece[p] ^= b_to;
	if (move_promotion(move)) {
		p = PAWN;
		cp = cpiece_make(PAWN, c);
	}
	board->piece[p] ^= b_from;
	board->color[c] ^= b_from | b_to;
	board->cpiece[to] = EMPTY;
	board->cpiece[from] = cp;
	// capture
	if (victim) {
		board->piece[cpiece_piece(victim)] ^= b_to;
		board->color[cpiece_color(victim)] ^= b_to;
		board->cpiece[to] = victim;
	}
	// enpassant capture
	if (p == PAWN && board->stack->enpassant == to) {
		const Square x = square(file(to), rank(from));
		const Bitboard b = x_to_bit(x);
		board->piece[PAWN] ^= b;
		board->color[opponent(c)] ^= b;
		board->cpiece[x] = cpiece_make(PAWN, opponent(c));
	}
	// king move
	if (p == KING) {
		board->x_king[c] = from;
		if (to == from + 2) board_deplace_piece(board, from + 1, from + 3);
		else if (to == from - 2) board_deplace_piece(board, from - 1, from - 4);
	}
}

/* Print the board. */
void board_print(const Board *board, FILE *output) {
	Square x;
	int f, r;
	const char p[] = ".PpNnBbRrQqKk#";
	const char c[] = "wb";
	const Square ep = board->stack->enpassant;

	fputs("  a b c d e f g h\n", output);
	for (r = 7; r >= 0; --r)
	for (f = 0; f <= 7; ++f) {
		x = square(f, r);
		if (f == 0) fprintf(output, "%1d ", r + 1);
		fputc(p[board->cpiece[x]], output); fputc(' ', output);
		if (f == 7) fprintf(output, "%1d\n", r + 1);
	}
	fputs("  a b c d e f g h\n", output);
	fprintf(output, "%c, ", c[board->player]);
	if (board->stack->castling & CAN_CASTLE_KINGSIDE[WHITE]) fputc('K', output);
	if (board->stack->castling & CAN_CASTLE_QUEENSIDE[WHITE]) fputc('Q', output);
	if (board->stack->castling & CAN_CASTLE_KINGSIDE[BLACK]) fputc('k', output);
	if (board->stack->castling & CAN_CASTLE_QUEENSIDE[BLACK]) fputc('q', output);
	if (board_enpassant(board))	fprintf(output, ", ep: %c%c", file(ep) + 'a', rank(ep) + '1');
	fprintf(output, "\n");
}


/* Check if a square is attacked.*/
bool board_is_square_attacked(const Board *board, const Square x, const Color c) {
	const Bitboard occupied = board->color[WHITE] + board->color[BLACK];
	const Bitboard C = board->color[c];

	return bishop_attack(occupied, x, C & (board->piece[BISHOP] | board->piece[QUEEN]))
	    || rook_attack(occupied, x, C & (board->piece[ROOK] | board->piece[QUEEN]))
	    || knight_attack(x, C & board->piece[KNIGHT])
	    || pawn_attack(x, opponent(c), C & board->piece[PAWN])
	    || king_attack(x, C & board->piece[KING]);
}

/* Append a move to an array of moves */
Move* push_move(Move *move, const Square from, const Square to) {
	*move++ = from | (to << 6);
	return move;
}

/* Append promotions from the same move */
Move* push_promotion(Move *move, const Square from, const Square to) {
	const Move m = from | (to << 6);

	*move++ = m | QUEEN_PROMOTION;
	*move++ = m | KNIGHT_PROMOTION;
	*move++ = m | ROOK_PROMOTION;
	*move++ = m | BISHOP_PROMOTION;
	return move;
}

/* Append all moves from a square */
Move* push_moves(Move *move, Bitboard attack, const Square from) {
	Square to;

	while (attack) {
		to = square_next(&attack);
		move = push_move(move, from, to);
	}
	return move;
}

/* Append all pawn moves from a direction */
Move* push_pawn_moves(Move *move, Bitboard attack, const int dir) {
	Square to;

	while (attack) {
		to = square_next(&attack);
		move = push_move(move, to - dir, to);
	}
	return move;
}

/* Append all promotions from a direction */
Move *push_promotions(Move *move, Bitboard attack, const int dir) {
	Square to;

	while (attack) {
		to = square_next(&attack);
		move = push_promotion(move, to - dir, to);
	}
	return move;
}

/* Generate all legal moves */
int generate_moves(Board *board, Move *move, const bool generate, const bool do_quiet) {
	const Color c = board->player;
	const Color o = opponent(c);
	const Bitboard occupied = board->color[WHITE] + board->color[BLACK];
	const Bitboard bq = board->piece[BISHOP] | board->piece[QUEEN];
	const Bitboard rq = board->piece[ROOK] | board->piece[QUEEN];
	const Bitboard pinned = board->stack->pinned;
	const Bitboard unpinned = board->color[c] & ~pinned;
	const Bitboard checkers = board->stack->checkers;
	const Square k = board->x_king[c];
	const int pawn_left = PUSH[c] - 1;
	const int pawn_right = PUSH[c] + 1;
	const int pawn_push = PUSH[c];
	const int *dir = DIRECTION[k];
	const Move *start = move;
	Bitboard target, piece, attack;
	Bitboard empty = ~occupied;
	Bitboard enemy = board->color[o];
	Square from, to, ep, x_checker = ENPASSANT_NONE;
	int d, count = 0;

	// in check: capture or block the (single) checker if any;
	if (checkers) {
		if (is_single(checkers)) {
			x_checker = square_first(checkers);
			empty = BETWEEN[k][x_checker];
			enemy = checkers;
		} else {
			empty = enemy  = 0;
		}

	// not in check: castling & pinned pieces moves
	} else {
		target = enemy; if (do_quiet) target |= empty;
		// castling
		if (do_quiet) {
			if ((board->stack->castling & CAN_CASTLE_KINGSIDE[c])
				&& (occupied & BETWEEN[k][k + 3]) == 0
				&& !board_is_square_attacked(board, k + 1, o)
				&& !board_is_square_attacked(board, k + 2, o)) {
					if (generate) move = push_move(move, k, k + 2); else ++count;
			}
			if ((board->stack->castling & CAN_CASTLE_QUEENSIDE[c])
				&& (occupied & BETWEEN[k][k - 4]) == 0
				&& !board_is_square_attacked(board, k - 1, o)
				&& !board_is_square_attacked(board, k - 2, o)) {
					if (generate) move = push_move(move, k, k - 2); else ++count;
			}
		}
		// pawn (pinned)
		piece = board->piece[PAWN] & pinned;
		while (piece) {
			from = square_next(&piece);
			d = dir[from];
			if (d == abs(pawn_left) && (x_to_bit(to = from + pawn_left) & pawn_attack(from, c, enemy))) {
				if (generate) move = is_on_seventh_rank(from, c) ? push_promotion(move, from, to) : push_move(move,from, to);
				else count += is_on_seventh_rank(from, c) ? 4 : 1;

			} else if (d == abs(pawn_right) && (x_to_bit(to = from + pawn_right) & pawn_attack(from, c, enemy))) {
				if (generate) move = is_on_seventh_rank(from, c) ? push_promotion(move, from, to) : push_move(move,from, to);
				else count += is_on_seventh_rank(from, c) ? 4 : 1;
			}
			if (do_quiet && d == abs(pawn_push) && (x_to_bit(to = from + pawn_push) & empty)) {
				if (generate) move = push_move(move, from, to); else ++count;
				if (is_on_second_rank(from, c) && (x_to_bit(to += pawn_push) & empty)) {
					if (generate) move = push_move(move, from, to); else ++count;
				}
			}
		}
		// bishop or queen (pinned)
		piece = bq & pinned;
		while (piece) {
			from = square_next(&piece);
			d = dir[from];
			attack = 0;
			if (d == 9) attack = diagonal_attack(occupied, from) & target;
			else if (d == 7) attack = antidiagonal_attack(occupied, from) & target;
			if (generate) move = push_moves(move, attack, from); else count += count_moves(attack);
		}
		// rook or queen (pinned)
		piece = rq & pinned;
		while (piece) {
			from = square_next(&piece);
			d = dir[from];
			attack = 0;
			if (d == 1) attack = rank_attack(occupied, from) & target; 
			else if (d == 8) attack = vertical_attack(occupied, from) & target;
			if (generate) move = push_moves(move, attack, from); else count += count_moves(attack);			
		}
	}
	// common moves

	target = enemy; if (do_quiet) target |= empty;

	// enpassant capture
	if (board_enpassant(board) && (!checkers || x_checker == board->stack->enpassant)) {
		to = board->stack->enpassant;
		ep = to - pawn_push;
		from = ep - 1;
		if (file(to) > 0 && board->cpiece[from] == cpiece_make(PAWN, c)) {
			piece = occupied ^ x_to_bit(from) ^ x_to_bit(ep) ^ x_to_bit(to);
			if (!bishop_attack(piece, k, bq & board->color[o]) && !rook_attack(piece, k, rq & board->color[o])) {
				if (generate) move = push_move(move, from, to); else ++count;
			}
		}
		from = ep + 1;
		if (file(to) < 7 && board->cpiece[from] == cpiece_make(PAWN, c)) {
			piece = occupied ^ x_to_bit(from) ^ x_to_bit(ep) ^ x_to_bit(to);
			if (!bishop_attack(piece, k, bq & board->color[o]) && !rook_attack(piece, k, rq & board->color[o])) {
				if (generate) move = push_move(move, from, to); else ++count;
			}
		}
	}

	// pawn
	piece = board->piece[PAWN] & unpinned;
	attack = (c ? (piece & ~FILE_A) >> 9 : (piece & ~FILE_A) << 7) & enemy;
	if (generate) {
		move = push_promotions(move, attack & PROMOTION_RANK[c], pawn_left);
		move = push_pawn_moves(move, attack & ~PROMOTION_RANK[c], pawn_left);
	} else count += 4 * count_moves(attack & PROMOTION_RANK[c]) + count_moves(attack & ~PROMOTION_RANK[c]);

	attack = (c ? (piece & ~FILE_H) >> 7 : (piece & ~FILE_H) << 9) & enemy;
	if (generate) {
		move = push_promotions(move, attack & PROMOTION_RANK[c], pawn_right);
		move = push_pawn_moves(move, attack & ~PROMOTION_RANK[c], pawn_right);
	} else count += 4 * count_moves(attack & PROMOTION_RANK[c]) + count_moves(attack & ~PROMOTION_RANK[c]);

	if (do_quiet) {
		attack = (c ? piece >> 8 : piece << 8) & empty;
		if (generate) {
			move = push_promotions(move, attack & PROMOTION_RANK[c], pawn_push);
			move = push_pawn_moves(move, attack & ~PROMOTION_RANK[c], pawn_push);
		} else count += 4 * count_moves(attack & PROMOTION_RANK[c]) + count_moves(attack & ~PROMOTION_RANK[c]);
		attack = (c ? (((piece & RANK_7) >> 8) & ~occupied) >> 8 : (((piece & RANK_2) << 8) & ~occupied) << 8) & empty;
		if (generate) move = push_pawn_moves(move, attack, 2 * pawn_push); else count += count_moves(attack);
	}

	// knight
	piece = board->piece[KNIGHT] & unpinned;
	while (piece) {
		from = square_next(&piece);
		attack = knight_attack(from, target);
		if (generate) move = push_moves(move, attack, from); else count += count_moves(attack);
	}

	// bishop or queen
	piece = bq & unpinned;
	while (piece) {
		from = square_next(&piece);
		attack = bishop_attack(occupied, from, target);
		if (generate) move = push_moves(move, attack, from); else count += count_moves(attack);
	}

	// rook or queen
	piece = rq & unpinned;
	while (piece) {
		from = square_next(&piece);
		attack = rook_attack(occupied, from, target);
		if (generate) move = push_moves(move, attack, from); else count += count_moves(attack);
	}

	// king
	board->color[c] ^= x_to_bit(k);
	target = board->color[o]; if (do_quiet) target |= ~occupied;
	attack = king_attack(k, target);
	while (attack) {
		to = square_next(&attack);
		if (!board_is_square_attacked(board, to, o)) {
			if (generate) move = push_move(move, k, to); else ++count;
		}
	}
	board->color[c] ^= x_to_bit(k);

	if (generate) count = move - start;

	return count;
}

/* Generate all legal moves or captures */
void movearray_generate(MoveArray *ma, Board *board,  const bool do_quiet) {
	ma->i = 0;
	ma->n = generate_moves(board, ma->move, true, do_quiet);
	ma->move[ma->n] = 0;
}

/* Get next move */
Move movearray_next(MoveArray *ma) {
	return ma->move[ma->i++];
}

/* Hash initialisation */
HashTable* hash_create(const int b) {
	const size_t n = 1ULL << b;
	size_t i;
	const Hash hash_init = {0, 0, 0};

	HashTable *hashtable = aligned_alloc(16, sizeof (HashTable));
	if (hashtable == NULL) memory_error(__func__);
	hashtable->hash = aligned_alloc(64, (n + BUCKET_SIZE) * sizeof (Hash));
	if (hashtable->hash == NULL) memory_error(__func__);
	hashtable->mask = n - 1;

	for (i = 0; i <= hashtable->mask + BUCKET_SIZE; ++i) hashtable->hash[i] = hash_init;

	return hashtable;
}

/* Hash free resources */
void hash_destroy(HashTable *hashtable) {
	if (hashtable) free(hashtable->hash);
	free(hashtable);
}

/* Hash probe */
uint64_t hash_probe(const HashTable *hashtable, const Key *key, const int depth) {
	Hash *hash = hashtable->hash + (key->index & hashtable->mask);

	for (int i = 0; i < BUCKET_SIZE; ++i) {
		if (hash[i].code == key->code && hash[i].depth == depth) return hash[i].count;
	}
	return 0;
}

/* Hash store */
void hash_store(const HashTable *hashtable, const Key *key, const int depth, const uint64_t count) {
	Hash *hash = (hashtable->hash + (key->index & hashtable->mask));
	int i, j;

	for (i = j = 0; i < BUCKET_SIZE; ++i) {
		if (hash[i].code == key->code && hash[i].depth == depth) return;
		if (hash[i].depth < hash[j].depth) j = i;
	}

	hash[j].code = key->code;
	hash[j].depth = depth;
	hash[j].count = count;
}

/* Prefetch */
void hash_prefetch(HashTable *hashtable, const Key *key) {
	#if defined(USE_GCC_X64)
		__builtin_prefetch(hashtable->hash + (key->index & hashtable->mask));
	#endif
}

/* Recursive Perft with optional hashtable, bulk counting & capture only generation */
uint64_t perft(Board *board, HashTable *hashtable, const int depth, const bool bulk, const bool do_quiet) {
	uint64_t count = 0;
	Move move;
	MoveArray ma[1];
	const Key *key = &board->stack->key;

	if (depth == 0) return 1;
	if (bulk && depth == 1) return generate_moves(board, NULL, false, do_quiet);
	if (hashtable && (count = hash_probe(hashtable, key, depth))) return count;

	movearray_generate(ma, board, do_quiet);

	while ((move = movearray_next(ma)) != 0) {
		board_update(board, move);
			if (hashtable && depth > 2) hash_prefetch(hashtable, &board->stack->key);
			count += perft(board, hashtable, depth - 1, bulk, do_quiet);
		board_restore(board, move);
	}
	if (hashtable) hash_store(hashtable, key, depth, count);

	return count;
}

/* main */
int main(int argc, char **argv) {
	double time = -chrono(), partial = 0.0;
	Board *board;
	HashTable *hashtable = NULL;
	Move move;
	MoveArray ma[1];
	unsigned long long count, total = 0;
	int i, d, depth = 6, hash_size = 0;
	bool div = false, capture = false, bulk = false, loop = false;
	char *fen = NULL;

	puts("HQPerft (c) Richard Delorme - 2017");
	puts("Bitboard move generation based on (H)yperbola (Q)uintessence & range attacks");

	// argument
	for (i = 1; i < argc; ++i) {
		if (!strcmp(argv[i], "--fen") || !strcmp(argv[i], "-f")) fen = argv[++i];
		else if (!strcmp(argv[i], "--depth") || !strcmp(argv[i], "-d")) depth = atoi(argv[++i]);
		else if (!strcmp(argv[i], "--bulk") || !strcmp(argv[i], "-b")) bulk = true;
		else if (!strcmp(argv[i], "--div") || !strcmp(argv[i], "-r")) div = true;
		else if (!strcmp(argv[i], "--capture") || !strcmp(argv[i], "-c")) capture = true;
		else if (!strcmp(argv[i], "--loop") || !strcmp(argv[i], "-l")) loop = true;
		else if (!strcmp(argv[i], "--hash") || !strcmp(argv[i], "-H")) hash_size = atoi(argv[++i]);
		else if (isdigit(argv[i][0])) depth = atoi(argv[i]);
		else {
			printf("%s [--fen|-f <fen>] [--depth|-d <depth>] [--hash|-H <size>] [--bulk|-b] [--div] [--capture] [--help|-h] \n", argv[0]);
			puts("Enumerate moves.");
			puts("\t--help|-h            Print this message.");
			puts("\t--fen|-f <fen>       Test the position indicated in FEN format (default=starting position).");
			puts("\t--depth|-d <depth>   Test up to this depth (default=6).");
			puts("\t--bulk|-b            Do fast bulk counting at the last ply.");
			puts("\t--hash|-H <size>     Use a hashtable with <size> bits entries (default 0, no hashtable).");
			puts("\t--capture|-c         Generate only captures.");
			puts("\t--loop|-l            Loop over .");
			puts("\t--div|-r             Print a node count for each move.");
			return i;
		}
	}
	
	// initialisation
	board_global_init();
	board = board_create();
	if (hash_size > 32) hash_size = 32;
	if (hash_size > 0) hashtable = hash_create(hash_size);
	if (fen) board_set(board, fen);
	if (depth < 1) depth = 1;

	printf("Perft setting: ");
	if (hash_size == 0) printf("no hashing; ");
	else printf("hashtable size: %u Mbytes; ", (unsigned) (sizeof (Hash) * (hashtable->mask + BUCKET_SIZE + 1) >> 20));
	if (bulk) printf("with"); else printf("no"); printf(" bulk counting;");
	if (capture) printf(" capture only;");
	puts("");
	board_print(board, stdout);

	// root search
	if (div) {
		movearray_generate(ma, board, !capture);
		while ((move = movearray_next(ma)) != 0) {
			board_update(board, move);
				count = perft(board, hashtable, depth - 1, bulk, !capture);
				total += count;
				printf("%5s %16llu\n", move_to_string(move, NULL), count);
			board_restore(board, move);
		}
	} else {
		for (d = (loop ? 1 : depth); d <= depth; ++d) {
			partial = -chrono();
			count = perft(board, hashtable, d, bulk, !capture);
			total += count;
			partial += chrono();
			printf("perft %2d : %15llu leaves in %10.3f s %12.0f leaves/s\n", d, count, partial, count / partial);
		}
	}
	time += chrono();
	if (div || loop) printf("perft %2d : %15llu leaves in %10.3f s %12.0f leaves/s\n", depth, total, time, total / time);

	board_destroy(board);
	hash_destroy(hashtable);

	return i;
}


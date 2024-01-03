#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
struct hashmap_of_i64_i64;
struct bucket_of_i64_i64;
struct bucket_state;
struct hashmap_iterator_of_i64_i64;
struct option_of_pointer_of_i64;
struct hashmap_of_i64_unit;
struct bucket_of_i64_unit;
struct result_of_unit_hashmap_error;
struct hashmap_error;
struct hashmap_insert_result_of_i64;
struct result_of_i64_pointer_of_i64;
enum bucket_state_tag {
    BUCKET_STATE_BUCKET_FREE_TAG,
    BUCKET_STATE_BUCKET_USED_TAG,
    BUCKET_STATE_BUCKET_DEAD_TAG
};
struct bucket_state {
    enum bucket_state_tag tag;
    union {

    } data;
};
struct bucket_of_i64_i64 {
    struct bucket_state state;
    int64_t hash;
    int64_t key;
    int64_t data;
};
typedef int64_t (*pointer_of_i64_to_i64)(int64_t *);
typedef bool (*pointer_of_i64_and_pointer_of_i64_to_bool)(int64_t *, int64_t *);
struct hashmap_of_i64_i64 {
    int64_t size;
    int64_t capacity;
    struct bucket_of_i64_i64 *buckets;
    pointer_of_i64_to_i64 hash_fn;
    pointer_of_i64_and_pointer_of_i64_to_bool compare_fn;
};
struct hashmap_iterator_of_i64_i64 {
    int64_t index;
    struct hashmap_of_i64_i64 *t;
};
enum option_of_pointer_of_i64_tag {
    OPTION_OF_POINTER_OF_I64_SOME_TAG,
    OPTION_OF_POINTER_OF_I64_NONE_TAG
};
struct option_of_pointer_of_i64 {
    enum option_of_pointer_of_i64_tag tag;
    union {
        int64_t *Some;
    } data;
};
struct bucket_of_i64_unit {
    struct bucket_state state;
    int64_t hash;
    int64_t key;
};
struct hashmap_of_i64_unit {
    int64_t size;
    int64_t capacity;
    struct bucket_of_i64_unit *buckets;
    pointer_of_i64_to_i64 hash_fn;
    pointer_of_i64_and_pointer_of_i64_to_bool compare_fn;
};
enum result_of_unit_hashmap_error_tag {
    RESULT_OF_UNIT_HASHMAP_ERROR_OK_TAG,
    RESULT_OF_UNIT_HASHMAP_ERROR_ERR_TAG
};
enum hashmap_error_tag {
    HASHMAP_ERROR_NOT_FOUND_TAG,
    HASHMAP_ERROR_DUPLICATE_TAG,
    HASHMAP_ERROR_FAILED_ALLOCATION_TAG
};
struct hashmap_error {
    enum hashmap_error_tag tag;
    union {

    } data;
};
struct result_of_unit_hashmap_error {
    enum result_of_unit_hashmap_error_tag tag;
    union {
        struct hashmap_error Err;
    } data;
};
enum hashmap_insert_result_of_i64_tag {
    HASHMAP_INSERT_RESULT_OF_I64_HASHMAP_DUPLICATE_TAG,
    HASHMAP_INSERT_RESULT_OF_I64_HASHMAP_INSERTED_TAG,
    HASHMAP_INSERT_RESULT_OF_I64_HASHMAP_FAILED_TAG
};
struct hashmap_insert_result_of_i64 {
    enum hashmap_insert_result_of_i64_tag tag;
    union {
        int64_t *Hashmap_duplicate;
        int64_t *Hashmap_inserted;
        struct hashmap_error Hashmap_failed;
    } data;
};
enum result_of_i64_pointer_of_i64_tag {
    RESULT_OF_I64_POINTER_OF_I64_OK_TAG,
    RESULT_OF_I64_POINTER_OF_I64_ERR_TAG
};
struct result_of_i64_pointer_of_i64 {
    enum result_of_i64_pointer_of_i64_tag tag;
    union {
        int64_t Ok;
        int64_t *Err;
    } data;
};
int64_t nearest_prime_helper(int64_t, int64_t, int64_t, int64_t);
int64_t main();
int64_t i64_hash_inst_i64(int64_t *);
bool i64_equal_inst_i64(int64_t *, int64_t *);
struct hashmap_of_i64_i64
    hashmap_create_inst_i64_i64(pointer_of_i64_to_i64,
                                pointer_of_i64_and_pointer_of_i64_to_bool);
struct hashmap_iterator_of_i64_i64
hashmap_iterator_inst_i64_i64(struct hashmap_of_i64_i64 *);
void print_hashmap_elements_inst_i64(struct hashmap_iterator_of_i64_i64 *);
struct option_of_pointer_of_i64
hashmap_iterator_next_inst_i64_i64(struct hashmap_iterator_of_i64_i64 *);
int print_int(int64_t);
int64_t nearest_prime(int64_t);
struct hashmap_of_i64_unit
    create_i64(pointer_of_i64_to_i64,
               pointer_of_i64_and_pointer_of_i64_to_bool);
struct hashmap_of_i64_unit
    hashmap_create_inst_i64_unit(pointer_of_i64_to_i64,
                                 pointer_of_i64_and_pointer_of_i64_to_bool);
bool cmp_i64(struct hashmap_of_i64_unit *, int64_t *, int64_t, int64_t);
bool bucket_compare_inst_i64_unit(struct hashmap_of_i64_unit *, int64_t *,
                                  int64_t, int64_t);
struct result_of_unit_hashmap_error resize_i64(struct hashmap_of_i64_i64 *,
                                               int64_t);
struct result_of_unit_hashmap_error
hashmap_resize_inst_i64_i64(struct hashmap_of_i64_i64 *, int64_t);
int64_t max_inst_i64(int64_t, int64_t);
struct bucket_of_i64_i64 *alloc_zeroed_inst_bucket_of_i64_i64(int64_t, int64_t);
struct bucket_of_i64_i64 *ptr_cast_inst_unit_bucket_of_i64_i64(void *);
void hashmap_insert_elements_inst_i64_i64(struct hashmap_of_i64_i64 *,
                                          struct bucket_of_i64_i64 *, int64_t,
                                          int64_t);
struct hashmap_insert_result_of_i64
hashmap_insert_inst_i64_i64(struct hashmap_of_i64_i64 *, int64_t, int64_t);
int64_t min_inst_i64(int64_t, int64_t);
struct result_of_i64_pointer_of_i64
hashmap_insert_loop_inst_i64_i64(struct hashmap_of_i64_i64 *, int64_t, int64_t,
                                 int64_t, int64_t, bool, int64_t);
bool bucket_compare_inst_i64_i64(struct hashmap_of_i64_i64 *, int64_t *,
                                 int64_t, int64_t);
void free_inst_bucket_of_i64_i64(struct bucket_of_i64_i64 *);
void *ptr_cast_inst_bucket_of_i64_i64_unit(struct bucket_of_i64_i64 *);
struct hashmap_insert_result_of_i64 insert_i64(struct hashmap_of_i64_i64 *,
                                               int64_t, int64_t);
int64_t random_inserts = 100;
int64_t test_size = 1000;
int64_t internal_8[] = {2,
                        3,
                        5,
                        7,
                        11,
                        13,
                        17,
                        19,
                        23,
                        29,
                        31,
                        37,
                        41,
                        43,
                        47,
                        53,
                        59,
                        61,
                        67,
                        71,
                        73,
                        79,
                        83,
                        89,
                        97,
                        103,
                        109,
                        113,
                        127,
                        137,
                        139,
                        149,
                        157,
                        167,
                        179,
                        193,
                        199,
                        211,
                        227,
                        241,
                        257,
                        277,
                        293,
                        313,
                        337,
                        359,
                        383,
                        409,
                        439,
                        467,
                        503,
                        541,
                        577,
                        619,
                        661,
                        709,
                        761,
                        823,
                        887,
                        953,
                        1031,
                        1109,
                        1193,
                        1289,
                        1381,
                        1493,
                        1613,
                        1741,
                        1879,
                        2029,
                        2179,
                        2357,
                        2549,
                        2753,
                        2971,
                        3209,
                        3469,
                        3739,
                        4027,
                        4349,
                        4703,
                        5087,
                        5503,
                        5953,
                        6427,
                        6949,
                        7517,
                        8123,
                        8783,
                        9497,
                        10273,
                        11113,
                        12011,
                        12983,
                        14033,
                        15173,
                        16411,
                        17749,
                        19183,
                        20753,
                        22447,
                        24281,
                        26267,
                        28411,
                        30727,
                        33223,
                        35933,
                        38873,
                        42043,
                        45481,
                        49201,
                        53201,
                        57557,
                        62233,
                        67307,
                        72817,
                        78779,
                        85229,
                        92203,
                        99733,
                        107897,
                        116731,
                        126271,
                        136607,
                        147793,
                        159871,
                        172933,
                        187091,
                        202409,
                        218971,
                        236897,
                        256279,
                        277261,
                        299951,
                        324503,
                        351061,
                        379787,
                        410857,
                        444487,
                        480881,
                        520241,
                        562841,
                        608903,
                        658753,
                        712697,
                        771049,
                        834181,
                        902483,
                        976369,
                        1056323,
                        1142821,
                        1236397,
                        1337629,
                        1447153,
                        1565659,
                        1693859,
                        1832561,
                        1982627,
                        2144977,
                        2320627,
                        2510653,
                        2716249,
                        2938679,
                        3179303,
                        3439651,
                        3721303,
                        4026031,
                        4355707,
                        4712381,
                        5098259,
                        5515729,
                        5967347,
                        6456007,
                        6984629,
                        7556579,
                        8175383,
                        8844859,
                        9569143,
                        10352717,
                        11200489,
                        12117689,
                        13109983,
                        14183539,
                        15345007,
                        16601593,
                        17961079,
                        19431899,
                        21023161,
                        22744717,
                        24607243,
                        26622317,
                        28802401,
                        31160981,
                        33712729,
                        36473443,
                        39460231,
                        42691603,
                        46187573,
                        49969847,
                        54061849,
                        58488943,
                        63278561,
                        68460391,
                        74066549,
                        80131819,
                        86693767,
                        93793069,
                        101473717,
                        109783337,
                        118773397,
                        128499677,
                        139022417,
                        150406843,
                        162723577,
                        176048909,
                        190465427,
                        206062531,
                        222936881,
                        241193053,
                        260944219,
                        282312799,
                        305431229,
                        330442829,
                        357502601,
                        386778277,
                        418451333,
                        452718089,
                        489790921,
                        529899637,
                        573292817,
                        620239453,
                        671030513,
                        725980837,
                        785430967,
                        849749479,
                        919334987,
                        994618837,
                        1076067617,
                        1164186217,
                        1259520799,
                        1362662261,
                        1474249943,
                        1594975441,
                        1725587117,
                        1866894511,
                        2019773507,
                        2185171673,
                        2364114217,
                        2557710269,
                        2767159799,
                        2993761039,
                        3238918481,
                        3504151727,
                        3791104843,
                        4101556399,
                        4294967291,
                        6442450933,
                        8589934583,
                        12884901857,
                        17179869143,
                        25769803693,
                        34359738337,
                        51539607367,
                        68719476731,
                        103079215087,
                        137438953447,
                        206158430123,
                        274877906899,
                        412316860387,
                        549755813881,
                        824633720731,
                        1099511627689,
                        1649267441579,
                        2199023255531,
                        3298534883309,
                        4398046511093,
                        6597069766607,
                        8796093022151,
                        13194139533241,
                        17592186044399,
                        26388279066581,
                        35184372088777,
                        52776558133177,
                        70368744177643,
                        105553116266399,
                        140737488355213,
                        211106232532861,
                        281474976710597,
                        562949953421231,
                        1125899906842597,
                        2251799813685119,
                        4503599627370449,
                        9007199254740881,
                        18014398509481951,
                        36028797018963913,
                        72057594037927931,
                        144115188075855859,
                        288230376151711717,
                        576460752303423433,
                        1152921504606846883,
                        2305843009213693951,
                        4611686018427387847,
                        4611686018427387847};
int64_t *primes = internal_8;
int64_t nearest_prime_helper(int64_t i, int64_t lo, int64_t hi, int64_t res) {
    int64_t internal_6;
    {
        if (((lo) > (hi))) {
            return res;
            ;
            ;
        } else {
            ;
        };
        int64_t mid;
        mid = ((((((hi) - (lo))) / (2))) + (lo));
        int64_t internal_7;
        if ((((primes)[mid]) > (i))) {
            int64_t internal_9;
            internal_9 = i;
            int64_t internal_10;
            internal_10 = lo;
            int64_t internal_11;
            internal_11 = ((mid) - (1));
            int64_t internal_12;
            internal_12 = (primes)[mid];
            internal_7 = (nearest_prime_helper)(internal_9, internal_10,
                                                internal_11, internal_12);
        } else {
            int64_t internal_13;
            internal_13 = i;
            int64_t internal_14;
            internal_14 = ((mid) + (1));
            int64_t internal_15;
            internal_15 = hi;
            int64_t internal_16;
            internal_16 = res;
            internal_7 = (nearest_prime_helper)(internal_13, internal_14,
                                                internal_15, internal_16);
        }
        internal_6 = internal_7;
    }
    return internal_6;
}
int64_t primes_size = 303;
int64_t i64_hash_inst_i64(int64_t *a) { return (*(a)); }
bool i64_equal_inst_i64(int64_t *a, int64_t *b) {
    return (((*(a))) == ((*(b))));
}
struct hashmap_of_i64_i64 hashmap_create_inst_i64_i64(
    pointer_of_i64_to_i64 hash_fn,
    pointer_of_i64_and_pointer_of_i64_to_bool compare_fn) {
    struct bucket_of_i64_i64 *internal_20;
    internal_20 = NULL;
    int64_t internal_21;
    internal_21 = 0;
    pointer_of_i64_and_pointer_of_i64_to_bool internal_22;
    internal_22 = compare_fn;
    pointer_of_i64_to_i64 internal_23;
    internal_23 = hash_fn;
    int64_t internal_24;
    internal_24 = 0;
    return (struct hashmap_of_i64_i64){.buckets = internal_20,
                                       .capacity = internal_21,
                                       .compare_fn = internal_22,
                                       .hash_fn = internal_23,
                                       .size = internal_24};
}
struct hashmap_iterator_of_i64_i64
hashmap_iterator_inst_i64_i64(struct hashmap_of_i64_i64 *t) {
    int64_t internal_29;
    internal_29 = 0;
    struct hashmap_of_i64_i64 *internal_30;
    internal_30 = t;
    return (struct hashmap_iterator_of_i64_i64){.index = internal_29,
                                                .t = internal_30};
}
struct option_of_pointer_of_i64
hashmap_iterator_next_inst_i64_i64(struct hashmap_iterator_of_i64_i64 *state) {
    struct option_of_pointer_of_i64 internal_32;
    {
        if ((((*(state)).index) > ((*((*(state)).t)).capacity))) {
            return (struct option_of_pointer_of_i64){
                .tag = OPTION_OF_POINTER_OF_I64_NONE_TAG};
            ;
            ;
        } else {
            ;
        };
        int64_t i;
        i = (*(state)).index;
        struct bucket_state internal_4;
        internal_4 = ((*((*(state)).t)).buckets)[i].state;
        struct option_of_pointer_of_i64 internal_33;
        if (((internal_4).tag == BUCKET_STATE_BUCKET_USED_TAG)) {
            struct option_of_pointer_of_i64 internal_34;
            {
                (*(state)).index = ((i) + (1));
                ;
                int64_t *internal_35;
                int64_t internal_36;
                internal_36 = ((*((*(state)).t)).buckets)[i].data;
                internal_35 = &(internal_36);
                internal_34 = (struct option_of_pointer_of_i64){
                    .tag = OPTION_OF_POINTER_OF_I64_SOME_TAG,
                    .data = {.Some = internal_35}};
            }
            internal_33 = internal_34;
        } else {
            struct option_of_pointer_of_i64 internal_37;
            if (true) {
                internal_4;
                struct hashmap_iterator_of_i64_i64 *internal_38;
                internal_38 = state;
                internal_37 = (hashmap_iterator_next_inst_i64_i64)(internal_38);
            } else {
                assert(false);
            }
            internal_33 = internal_37;
        }
        internal_32 = internal_33;
    }
    return internal_32;
}
int print_int(int64_t i) {
    int internal_40;
    {
        int64_t curr;
        curr = ((i) % (10));
        if (((((i) / (10))) > (0))) {
            int64_t internal_41;
            internal_41 = ((i) / (10));
            (print_int)(internal_41);
            ;
        } else {
            ;
        };
        int internal_42;
        internal_42 = (int)((curr) + ((int64_t)("0")[0]));
        void *internal_43;
        internal_43 = stdout;
        internal_40 = (fputc)(internal_42, internal_43);
    }
    return internal_40;
}
void print_hashmap_elements_inst_i64(struct hashmap_iterator_of_i64_i64 *it) {
    {
        struct option_of_pointer_of_i64 internal_5;
        struct hashmap_iterator_of_i64_i64 *internal_31;
        internal_31 = it;
        internal_5 = (hashmap_iterator_next_inst_i64_i64)(internal_31);
        if (((internal_5).tag == OPTION_OF_POINTER_OF_I64_NONE_TAG)) {
            ;
        } else {
            if (((((internal_5).tag == OPTION_OF_POINTER_OF_I64_SOME_TAG))
                 && (true))) {
                int64_t x;
                x = (*((internal_5).data.Some));
                {
                    int64_t internal_39;
                    internal_39 = x;
                    (print_int)(internal_39);
                    char *internal_44;
                    internal_44 = "";
                    (puts)(internal_44);
                    ;
                };
            } else {
                assert(false);
            };
        };
    }
}
int64_t main() {
    int64_t internal_17;
    {
        struct hashmap_of_i64_i64 t;
        pointer_of_i64_to_i64 internal_18;
        internal_18 = i64_hash_inst_i64;
        pointer_of_i64_and_pointer_of_i64_to_bool internal_19;
        internal_19 = i64_equal_inst_i64;
        t = (hashmap_create_inst_i64_i64)(internal_18, internal_19);
        struct hashmap_iterator_of_i64_i64 *internal_25;
        struct hashmap_iterator_of_i64_i64 internal_26;
        struct hashmap_of_i64_i64 *internal_27;
        struct hashmap_of_i64_i64 internal_28;
        internal_28 = t;
        internal_27 = &(internal_28);
        internal_26 = (hashmap_iterator_inst_i64_i64)(internal_27);
        internal_25 = &(internal_26);
        (print_hashmap_elements_inst_i64)(internal_25);
        internal_17 = 0;
    }
    return internal_17;
}
int64_t hashmap_min_capacity = 17;
int64_t random_max = 1000;
int64_t hashmap_max_load = 600;
int64_t nearest_prime(int64_t i) {
    int64_t internal_45;
    internal_45 = i;
    int64_t internal_46;
    internal_46 = 0;
    int64_t internal_47;
    internal_47 = primes_size;
    int64_t internal_48;
    internal_48 = 0;
    return (nearest_prime_helper)(internal_45, internal_46, internal_47,
                                  internal_48);
}
struct hashmap_of_i64_unit hashmap_create_inst_i64_unit(
    pointer_of_i64_to_i64 hash_fn,
    pointer_of_i64_and_pointer_of_i64_to_bool compare_fn) {
    struct bucket_of_i64_unit *internal_51;
    internal_51 = NULL;
    int64_t internal_52;
    internal_52 = 0;
    pointer_of_i64_and_pointer_of_i64_to_bool internal_53;
    internal_53 = compare_fn;
    pointer_of_i64_to_i64 internal_54;
    internal_54 = hash_fn;
    int64_t internal_55;
    internal_55 = 0;
    return (struct hashmap_of_i64_unit){.buckets = internal_51,
                                        .capacity = internal_52,
                                        .compare_fn = internal_53,
                                        .hash_fn = internal_54,
                                        .size = internal_55};
}
struct hashmap_of_i64_unit
create_i64(pointer_of_i64_to_i64 hash_fn,
           pointer_of_i64_and_pointer_of_i64_to_bool compare_fn) {
    pointer_of_i64_to_i64 internal_49;
    internal_49 = hash_fn;
    pointer_of_i64_and_pointer_of_i64_to_bool internal_50;
    internal_50 = compare_fn;
    return (hashmap_create_inst_i64_unit)(internal_49, internal_50);
}
bool bucket_compare_inst_i64_unit(struct hashmap_of_i64_unit *t, int64_t *key,
                                  int64_t h, int64_t i) {
    int64_t *internal_60;
    int64_t internal_61;
    internal_61 = ((*(t)).buckets)[i].key;
    internal_60 = &(internal_61);
    int64_t *internal_62;
    internal_62 = key;
    return ((((((*(t)).buckets)[i].hash) == (h)))
            && (((*(t)).compare_fn)(internal_60, internal_62)));
}
bool cmp_i64(struct hashmap_of_i64_unit *t, int64_t *key, int64_t h,
             int64_t i) {
    struct hashmap_of_i64_unit *internal_56;
    internal_56 = t;
    int64_t *internal_57;
    internal_57 = key;
    int64_t internal_58;
    internal_58 = h;
    int64_t internal_59;
    internal_59 = i;
    return (bucket_compare_inst_i64_unit)(internal_56, internal_57, internal_58,
                                          internal_59);
}
int64_t max_inst_i64(int64_t a, int64_t b) {
    int64_t internal_68;
    if (((a) > (b))) {
        internal_68 = a;
    } else {
        internal_68 = b;
    }
    return internal_68;
}
struct bucket_of_i64_i64 *ptr_cast_inst_unit_bucket_of_i64_i64(void *x) {
    return (struct bucket_of_i64_i64 *)x;
}
struct bucket_of_i64_i64 *
alloc_zeroed_inst_bucket_of_i64_i64(int64_t num_elements, int64_t element_sz) {
    void *internal_72;
    int64_t internal_73;
    internal_73 = num_elements;
    int64_t internal_74;
    internal_74 = element_sz;
    internal_72 = (calloc)(internal_73, internal_74);
    return (ptr_cast_inst_unit_bucket_of_i64_i64)(internal_72);
}
int64_t min_inst_i64(int64_t a, int64_t b) {
    int64_t internal_86;
    if (((a) < (b))) {
        internal_86 = a;
    } else {
        internal_86 = b;
    }
    return internal_86;
}
bool bucket_compare_inst_i64_i64(struct hashmap_of_i64_i64 *t, int64_t *key,
                                 int64_t h, int64_t i) {
    int64_t *internal_111;
    int64_t internal_112;
    internal_112 = ((*(t)).buckets)[i].key;
    internal_111 = &(internal_112);
    int64_t *internal_113;
    internal_113 = key;
    return ((((((*(t)).buckets)[i].hash) == (h)))
            && (((*(t)).compare_fn)(internal_111, internal_113)));
}
struct result_of_i64_pointer_of_i64
hashmap_insert_loop_inst_i64_i64(struct hashmap_of_i64_i64 *t, int64_t key,
                                 int64_t h, int64_t cnt, int64_t i,
                                 bool found_dead, int64_t dead_i) {
    struct result_of_i64_pointer_of_i64 internal_101;
    {
        if (((cnt) > ((*(t)).capacity))) {
            int64_t internal_102;
            int64_t internal_103;
            if (found_dead) {
                internal_103 = dead_i;
            } else {
                internal_103 = i;
            }
            internal_102 = internal_103;
            return (struct result_of_i64_pointer_of_i64){
                .tag = RESULT_OF_I64_POINTER_OF_I64_OK_TAG,
                .data = {.Ok = internal_102}};
            ;
            ;
        } else {
            ;
        };
        struct bucket_state internal_1;
        internal_1 = ((*(t)).buckets)[i].state;
        if (((internal_1).tag == BUCKET_STATE_BUCKET_FREE_TAG)) {
            int64_t internal_104;
            int64_t internal_105;
            if (found_dead) {
                internal_105 = dead_i;
            } else {
                internal_105 = i;
            }
            internal_104 = internal_105;
            return (struct result_of_i64_pointer_of_i64){
                .tag = RESULT_OF_I64_POINTER_OF_I64_OK_TAG,
                .data = {.Ok = internal_104}};
            ;
        } else {
            if (((internal_1).tag == BUCKET_STATE_BUCKET_USED_TAG)) {
                {
                    struct hashmap_of_i64_i64 *internal_106;
                    internal_106 = t;
                    int64_t *internal_107;
                    int64_t internal_108;
                    internal_108 = key;
                    internal_107 = &(internal_108);
                    int64_t internal_109;
                    internal_109 = h;
                    int64_t internal_110;
                    internal_110 = i;
                    if ((bucket_compare_inst_i64_i64)(internal_106,
                                                      internal_107,
                                                      internal_109,
                                                      internal_110)) {
                        int64_t *internal_114;
                        int64_t internal_115;
                        internal_115 = ((*(t)).buckets)[i].data;
                        internal_114 = &(internal_115);
                        return (struct result_of_i64_pointer_of_i64){
                            .tag = RESULT_OF_I64_POINTER_OF_I64_ERR_TAG,
                            .data = {.Err = internal_114}};
                        ;
                        ;
                    } else {
                        ;
                    };
                };
            } else {
                if (((internal_1).tag == BUCKET_STATE_BUCKET_DEAD_TAG)) {
                    {
                        if (((found_dead) == (false))) {
                            {
                                found_dead = true;
                                ;
                                dead_i = i;
                                ;
                                ;
                            };
                            ;
                        } else {
                            ;
                        };
                    };
                } else {
                    assert(false);
                };
            };
        };
        struct hashmap_of_i64_i64 *internal_116;
        internal_116 = t;
        int64_t internal_117;
        internal_117 = key;
        int64_t internal_118;
        internal_118 = h;
        int64_t internal_119;
        internal_119 = ((cnt) + (1));
        int64_t internal_120;
        internal_120 = ((((i) + (1))) % ((*(t)).capacity));
        bool internal_121;
        internal_121 = found_dead;
        int64_t internal_122;
        internal_122 = dead_i;
        internal_101 =
            (hashmap_insert_loop_inst_i64_i64)(internal_116, internal_117,
                                               internal_118, internal_119,
                                               internal_120, internal_121,
                                               internal_122);
    }
    return internal_101;
}
struct hashmap_insert_result_of_i64
hashmap_insert_inst_i64_i64(struct hashmap_of_i64_i64 *t, int64_t key,
                            int64_t data) {
    struct hashmap_insert_result_of_i64 internal_83;
    {
        int64_t sz;
        int64_t internal_84;
        internal_84 = (*(t)).size;
        int64_t internal_85;
        internal_85 = 1;
        sz = (min_inst_i64)(internal_84, internal_85);
        int64_t load;
        int64_t internal_87;
        internal_87 = (*(t)).capacity;
        int64_t internal_88;
        internal_88 = 1;
        load = ((((sz) * (1000))) / ((min_inst_i64)(internal_87, internal_88)));
        if (((load) > (hashmap_max_load))) {
            {
                struct result_of_unit_hashmap_error internal_0;
                struct hashmap_of_i64_i64 *internal_89;
                internal_89 = t;
                int64_t internal_90;
                internal_90 = ((sz) * (2));
                internal_0 =
                    (hashmap_resize_inst_i64_i64)(internal_89, internal_90);
                if (((((internal_0).tag == RESULT_OF_UNIT_HASHMAP_ERROR_OK_TAG))
                     && (true))) {
                    ;
                } else {
                    if (((((internal_0).tag
                           == RESULT_OF_UNIT_HASHMAP_ERROR_ERR_TAG))
                         && (true))) {
                        struct hashmap_error e;
                        e = (internal_0).data.Err;
                        struct hashmap_error internal_91;
                        internal_91 = e;
                        return (struct hashmap_insert_result_of_i64){
                            .tag =
                                HASHMAP_INSERT_RESULT_OF_I64_HASHMAP_FAILED_TAG,
                            .data = {.Hashmap_failed = internal_91}};
                        ;
                    } else {
                        assert(false);
                    };
                };
            };
            ;
        } else {
            ;
        };
        int64_t h;
        int64_t *internal_92;
        int64_t internal_93;
        internal_93 = key;
        internal_92 = &(internal_93);
        h = ((*(t)).hash_fn)(internal_92);
        int64_t index;
        index = ((h) % ((*(t)).capacity));
        struct result_of_i64_pointer_of_i64 internal_2;
        struct hashmap_of_i64_i64 *internal_94;
        internal_94 = t;
        int64_t internal_95;
        internal_95 = key;
        int64_t internal_96;
        internal_96 = h;
        int64_t internal_97;
        internal_97 = 0;
        int64_t internal_98;
        internal_98 = index;
        bool internal_99;
        internal_99 = false;
        int64_t internal_100;
        internal_100 = 0;
        internal_2 =
            (hashmap_insert_loop_inst_i64_i64)(internal_94, internal_95,
                                               internal_96, internal_97,
                                               internal_98, internal_99,
                                               internal_100);
        struct hashmap_insert_result_of_i64 internal_123;
        if (((((internal_2).tag == RESULT_OF_I64_POINTER_OF_I64_ERR_TAG))
             && (true))) {
            int64_t *e;
            e = (internal_2).data.Err;
            int64_t *internal_124;
            internal_124 = e;
            internal_123 = (struct hashmap_insert_result_of_i64){
                .tag = HASHMAP_INSERT_RESULT_OF_I64_HASHMAP_DUPLICATE_TAG,
                .data = {.Hashmap_duplicate = internal_124}};
        } else {
            struct hashmap_insert_result_of_i64 internal_125;
            if (((((internal_2).tag == RESULT_OF_I64_POINTER_OF_I64_OK_TAG))
                 && (true))) {
                int64_t i;
                i = (internal_2).data.Ok;
                struct hashmap_insert_result_of_i64 internal_126;
                {
                    ((*(t)).buckets)[i].hash = h;
                    ;
                    ((*(t)).buckets)[i].state = (struct bucket_state){
                        .tag = BUCKET_STATE_BUCKET_USED_TAG};
                    ;
                    ((*(t)).buckets)[i].key = key;
                    ;
                    ((*(t)).buckets)[i].data = data;
                    ;
                    (*(t)).size = (((*(t)).size) + (1));
                    ;
                    int64_t *internal_127;
                    int64_t internal_128;
                    internal_128 = ((*(t)).buckets)[i].data;
                    internal_127 = &(internal_128);
                    internal_126 = (struct hashmap_insert_result_of_i64){
                        .tag =
                            HASHMAP_INSERT_RESULT_OF_I64_HASHMAP_INSERTED_TAG,
                        .data = {.Hashmap_inserted = internal_127}};
                }
                internal_125 = internal_126;
            } else {
                assert(false);
            }
            internal_123 = internal_125;
        }
        internal_83 = internal_123;
    }
    return internal_83;
}
void hashmap_insert_elements_inst_i64_i64(struct hashmap_of_i64_i64 *t,
                                          struct bucket_of_i64_i64 *old_buckets,
                                          int64_t old_capacity, int64_t i) {
    {
        if (((i) > (old_capacity))) {
            return;
            ;
            ;
        } else {
            ;
        };
        struct bucket_state internal_3;
        internal_3 = (old_buckets)[i].state;
        if (((internal_3).tag == BUCKET_STATE_BUCKET_USED_TAG)) {
            {
                struct hashmap_of_i64_i64 *internal_80;
                internal_80 = t;
                int64_t internal_81;
                internal_81 = (old_buckets)[i].key;
                int64_t internal_82;
                internal_82 = (old_buckets)[i].data;
                (hashmap_insert_inst_i64_i64)(internal_80, internal_81,
                                              internal_82);
                ;
            };
        } else {
            if (true) {
                internal_3;
                ;
            } else {
                assert(false);
            };
        };
        struct hashmap_of_i64_i64 *internal_129;
        internal_129 = t;
        struct bucket_of_i64_i64 *internal_130;
        internal_130 = old_buckets;
        int64_t internal_131;
        internal_131 = old_capacity;
        int64_t internal_132;
        internal_132 = ((i) + (1));
        (hashmap_insert_elements_inst_i64_i64)(internal_129, internal_130,
                                               internal_131, internal_132);
    }
}
void *ptr_cast_inst_bucket_of_i64_i64_unit(struct bucket_of_i64_i64 *x) {
    return (void *)x;
}
void free_inst_bucket_of_i64_i64(struct bucket_of_i64_i64 *a) {
    void *internal_134;
    struct bucket_of_i64_i64 *internal_135;
    internal_135 = a;
    internal_134 = (ptr_cast_inst_bucket_of_i64_i64_unit)(internal_135);
}
struct result_of_unit_hashmap_error
hashmap_resize_inst_i64_i64(struct hashmap_of_i64_i64 *t,
                            int64_t new_capacity) {
    struct result_of_unit_hashmap_error internal_65;
    {
        int64_t internal_66;
        internal_66 = new_capacity;
        int64_t internal_67;
        internal_67 = hashmap_min_capacity;
        new_capacity = (max_inst_i64)(internal_66, internal_67);
        ;
        int64_t internal_69;
        internal_69 = new_capacity;
        new_capacity = (nearest_prime)(internal_69);
        ;
        struct bucket_of_i64_i64 *new_buckets;
        int64_t internal_70;
        internal_70 = new_capacity;
        int64_t internal_71;
        internal_71 = sizeof(struct bucket_of_i64_i64);
        new_buckets =
            (alloc_zeroed_inst_bucket_of_i64_i64)(internal_70, internal_71);
        if (((new_buckets) == (NULL))) {
            struct hashmap_error internal_75;
            internal_75 = (struct hashmap_error){
                .tag = HASHMAP_ERROR_FAILED_ALLOCATION_TAG};
            return (struct result_of_unit_hashmap_error){
                .tag = RESULT_OF_UNIT_HASHMAP_ERROR_ERR_TAG,
                .data = {.Err = internal_75}};
            ;
            ;
        } else {
            ;
        };
        struct bucket_of_i64_i64 *old_buckets;
        old_buckets = (*(t)).buckets;
        int64_t old_capacity;
        old_capacity = (*(t)).capacity;
        (*(t)).size = 0;
        ;
        (*(t)).capacity = new_capacity;
        ;
        (*(t)).buckets = new_buckets;
        ;
        struct hashmap_of_i64_i64 *internal_76;
        internal_76 = t;
        struct bucket_of_i64_i64 *internal_77;
        internal_77 = old_buckets;
        int64_t internal_78;
        internal_78 = old_capacity;
        int64_t internal_79;
        internal_79 = 0;
        (hashmap_insert_elements_inst_i64_i64)(internal_76, internal_77,
                                               internal_78, internal_79);
        struct bucket_of_i64_i64 *internal_133;
        internal_133 = old_buckets;
        (free_inst_bucket_of_i64_i64)(internal_133);
        internal_65 = (struct result_of_unit_hashmap_error){
            .tag = RESULT_OF_UNIT_HASHMAP_ERROR_OK_TAG};
    }
    return internal_65;
}
struct result_of_unit_hashmap_error resize_i64(struct hashmap_of_i64_i64 *t,
                                               int64_t sz) {
    struct hashmap_of_i64_i64 *internal_63;
    internal_63 = t;
    int64_t internal_64;
    internal_64 = sz;
    return (hashmap_resize_inst_i64_i64)(internal_63, internal_64);
}
int64_t hashmap_min_load_after_remove = 100;
struct hashmap_insert_result_of_i64 insert_i64(struct hashmap_of_i64_i64 *t,
                                               int64_t key, int64_t data) {
    struct hashmap_of_i64_i64 *internal_136;
    internal_136 = t;
    int64_t internal_137;
    internal_137 = key;
    int64_t internal_138;
    internal_138 = data;
    return (hashmap_insert_inst_i64_i64)(internal_136, internal_137,
                                         internal_138);
}

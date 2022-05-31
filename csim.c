/* 
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss. (I examined the trace,
 *     the largest request I saw was for 8 bytes).
 *  2. Instruction loads (I) are ignored, since we are only interested in evaluating
 *     data cache performance.
 *  3. Data modify (M) is treated as a load followed by a store to the same
 *     address. Hence, an M operation can result in two cache hits, or a miss and a
 *     hit plus an possible eviction.
 *
 */
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>

#include <stdint.h>  //Fyrir uint í struct

//Macro dót fyrir bit-twiddling
#define MASK(x)                    ((1 << x) - 1)
#define EXTRACT_SET_INDEX(addr)    ((addr & (MASK(s) << b)) >> b)
#define EXTRACT_BLOCK_OFFSET(addr) ((addr & MASK(b)))
#define EXTRACT_TAG_BITS(addr)     ((addr & (~MASK((s+b)))) >> (s+b))

/* Type: Memory address */
typedef unsigned long long int mem_addr_t;

/* Globals set by command line args */
int s = 0; /* set index bits */
int b = 0; /* block offset bits */
int E = 0; /* associativity */
char* trace_file = NULL;

/* Derived from command line args */
int S; /* number of sets */
int B; /* block size (bytes) */

/* Counters used to record cache statistics */
int miss_count = 0;
int hit_count = 0;
int eviction_count = 0;
unsigned long long int lru_counter = 1;

/* Skyndiminnið okkar er pointer að Set */
typedef struct Set * Cache;
/* Global breyta fyrir cache */
Cache cache;

/* Forward declaration */
void freeCache();

struct Block{
    uint8_t valid :1;
    uint32_t tag;
    unsigned long lru;
};

struct Set {
    uint32_t set_id;
    struct Block * block_array;
};

typedef struct best_result {
    int e,b,s;
    int hits, misses, evictions;
    float miss_ratio;
} best_result_t;

struct Block *init_block(int number_of_blocks){
    struct Block *bl = malloc(sizeof(struct Block) * number_of_blocks);

    for (int i = 0; i < number_of_blocks; i++) {
        bl[i].valid = 0;
        bl[i].tag = 0;
        bl[i].lru = 0;
    }

    return bl;
}

struct Set *init_set(int number_of_sets, int number_of_blocks){
    struct Set *set = malloc(sizeof(struct Set) * number_of_sets);

    for (int i = 0; i < number_of_sets; i++) {
        set[i].set_id = i;
        set[i].block_array = init_block(number_of_blocks);
    }

    return set;
}

// Test fall, fyrir debugging og annað
#ifdef DEBUG
void print_cache(struct Set *st, int number_of_sets, int number_of_blocks){
    printf("Block: %ld\n",sizeof(struct Block));
    for (int i = 0; i < number_of_sets; i++) {
        printf("Set: %d\n", st[i].set_id);
        for (int j = 0; j < number_of_blocks; j++) {
            printf("block %d::\t valid: %d " ,j,st[i].block_array[j].valid);
            printf("tag: %d " ,st[i].block_array[j].tag);
            printf("lru: %ld \n" ,st[i].block_array[j].lru);
        }
        printf("\n");
    }
}
#endif

/* initCache - Allocate memory, write 0's for valid and tag and LRU */
void initCache(void) {
    cache = init_set(S, E);

    //Debug func
#ifdef DEBUG
    print_cache(cache,S,E);
#endif
}

#ifdef DEBUG
//Test: Fjarlægja seinna eða breyta í Macro
void extract_set_bits(mem_addr_t addr){
    /* mem_addr_t mask = MASK(s); */
    /* printf("Mask: %llx\n" ,mask); */
    /* printf("Addr: %llx\n" ,addr); */

    /* unsigned long long t = (add & (mask << B)) >> B; */
    mem_addr_t t = EXTRACT_SET_INDEX(addr);
    printf("Set:%llu\n" ,t);
}

//Test: Fjarlægja seinna eða breyta í Macro
void extract_tag_bits(mem_addr_t addr){
    int offset = s+b;
    mem_addr_t mask = ~MASK(offset);

    printf("Mask: %llx\n" ,mask);
    printf("Addr: %llx\n" ,addr);

    /* mem_addr_t t = (addr & (~MASK((s+b)))); */
    printf("Tag: %llx\n" , (EXTRACT_TAG_BITS(addr) ));
}

void extract_block_offset(mem_addr_t addr){
    mem_addr_t mask = MASK(b);

    printf("Mask: %llx\n" ,mask);
    printf("Addr: %llx\n" ,addr);

    /* mem_addr_t t = (addr & (mask)); */
    printf("Block Offset: %llu\n", (EXTRACT_BLOCK_OFFSET(addr)));
}
#endif

/* freeCache - free allocated memory */
// Clang kvartar stundum yfir þessu, skoða betur? Valgrind segir að allt sé í
// lagi hér!
void freeCache() {
    for (int i = 0; i < S; i++) {
        free(cache[i].block_array);
    }
    free(cache);
}


void evict_lru(int set){
    unsigned long long min = cache[set].block_array[0].lru;
    int lru_E = 0;
    for (int j = 0; j < E; j++) {
        if(cache[set].block_array[j].lru < min){
            min = cache[set].block_array[j].lru;
            lru_E = j;
        }
    }

    cache[set].block_array[lru_E].valid = 0;
    cache[set].block_array[lru_E].tag = 0;
    cache[set].block_array[lru_E].lru = 0;

    eviction_count++;
}

void set_full(int set) {
    for (int i = 0; i < E; i++) {
        if(cache[set].block_array[i].tag == 0){
            return;
        }
    }
    evict_lru(set);
    return;
}

/* 
 * accessData - Access data at memory address addr.
 *   If it is already in cache, increast hit_count
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Also increase eviction_count if a line is evicted.
 */
void accessData(mem_addr_t addr) {
    lru_counter++;
    int set = EXTRACT_SET_INDEX(addr);
    for (int i = 0; i < E; i++) {
        if(cache[set].block_array[i].tag == EXTRACT_TAG_BITS(addr)){
            hit_count++;
            cache[set].block_array[i].lru = lru_counter;
            return;
        }   
    }

    for (int i = 0; i < E; i++) {
        if (!cache[set].block_array[i].valid) {
            cache[set].block_array[i].lru = lru_counter;
            cache[set].block_array[i].tag = EXTRACT_TAG_BITS(addr);
            cache[set].block_array[i].valid= 1;
            miss_count++;
            return;
        }
    }

    //Athuga hvort er fullt, fjarlægjum ef svo er og setjum gildið svo í cache
    set_full(set);

    accessData(addr);
}


/* replayTrace - replays the given trace file against the cache */ 
void replayTrace(char* trace_fn) {
    char buf[1000];
    mem_addr_t addr=0;
    unsigned int len=0;
    FILE* trace_fp = fopen(trace_fn, "r");

    if(!trace_fp){
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);
    }

    while(fgets(buf, 1000, trace_fp) != NULL) {
        if(buf[1]=='S' || buf[1]=='L' || buf[1]=='M') {
            sscanf(buf+3, "%llx,%u", &addr, &len);
      
            accessData(addr);

            /* If the instruction is R/W then access again */
            if(buf[1]=='M')
                accessData(addr);
        }
    }

    fclose(trace_fp);
}

/* printSummary - Summarize the cache simulation statistics */
void printSummary(int hits, int misses, int evictions) {
    printf("hits: %d  misses: %d  evictions: %d\n", hits, misses, evictions);
    printf("miss ratio: %.2f%%\n", 100.0*misses/(hits+misses));
    printf("S: %d, B: %d E: %d\n" ,S,B,E);
}

/* printUsage - Print usage info */
void printUsage(char* argv[]) {
    printf("Usage: %s [-h] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}



void print_best(best_result_t best){
    printf("==========================================");
    printf("\n Best:\n");
    printf("E:%d\t b:%d\t s:%d\t \n",E,b,s);
    printSummary(best.hits, best.misses, best.evictions);
}

void best_test(char* trace_file){
    printf("Finnur bestu uppsetningu...\n");
    best_result_t best_result;
    best_result.miss_ratio = 100.0;

    for (int i = 4; i <= 6; i++) {
        for (int e = 0; e < 4; e++) {
            miss_count = 0;
            hit_count = 0;
            eviction_count = 0;

            E = (1 << e);
            b = i;
            s = 14 - ((b+e)); //16kb eru 2^14

            /* Compute S, E and B from command line args */
            S = (unsigned int) (1 << s);
            B = (unsigned int) (1 << b);

            /* Initialize cache */
            initCache();

            /* Run the simulation */
            replayTrace(trace_file);

#ifdef DEBUG
            print_cache(cache,S,E);
#endif

            /* Skrifa niðurstöður í best_result */
            if((100.0*miss_count/(hit_count+miss_count)) < best_result.miss_ratio ) {
                best_result = (best_result_t) {E,b,s,hit_count,miss_count,eviction_count};
                best_result.miss_ratio = (100.0*miss_count/(hit_count+miss_count));
            }

            /* Free allocated memory */
            freeCache();

            /* Output the hit and miss statistics */
            printf("E:%d\t b:%d\t s:%d\t \n",E,b,s);
            printSummary(hit_count, miss_count, eviction_count);
        }   
    }
    print_best(best_result);
}

/* main - Main routine */ 
int main(int argc, char* argv[]) {
    char c;
    int m = 0;

    while( (c=getopt(argc,argv,"s:E:b:t:hm")) != -1){
        switch(c){
        case 's':
            s = atoi(optarg);
            break;
        case 'E':
            E = atoi(optarg);
            break;
        case 'b':
            b = atoi(optarg);
            break;
        case 't':
            trace_file = optarg;
            break;
        case 'h':
            printUsage(argv);
            exit(0);
        case 'm':
            m = 1;
            break;
        default:
            printUsage(argv);
            exit(1);
        }
    }

    if(m == 1){
        best_test(trace_file);
        exit(1);
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        printUsage(argv);
        exit(1);
    }

    /* Compute S, E and B from command line args */
    S = (unsigned int) (1 << s);
    B = (unsigned int) (1 << b);

 
    /* Initialize cache */
    initCache();

//Nokkur vistföng notuð í prófunum
#ifdef DEBUG
    printf("S: %d\nB: %d\n", S, B);
    printf("s: %d\nb: %d\n", s, b);
    extract_set_bits(0x3072620ef0);
    extract_set_bits(0x7ff0005f8);
    extract_set_bits(0x307241af2c);

    printf("\nTag bits:\n");
    extract_tag_bits(0x3072620ef0);
    extract_tag_bits(0x7ff0005f8);
    extract_tag_bits(0x307241af2c);

    printf("\nBlock bits:\n");
    extract_block_offset(0x3072620ef0);
    extract_block_offset(0x7ff0005f8);
    extract_block_offset(0x307241af2c);
#endif

    /* Run the simulation */
    replayTrace(trace_file);

#ifdef DEBUG
    print_cache(cache,S,E);
#endif

    /* Free allocated memory */
    freeCache();

    /* Output the hit and miss statistics */
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}

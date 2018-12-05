#ifndef __CONFIG_H_
#define __CONFIG_H_

/*
 * config.h - malloc lab configuration file
 *
 * Copyright (c) 2002, R. Bryant and D. O'Hallaron, All rights reserved.
 * May not be used, modified, or copied without permission.
 */

/*
 * This is the default path where the driver will look for the
 * default tracefiles. You can override it at runtime with the -t flag.
 */
#define TRACEDIR "./traces/"

/*
 * This is the list of default tracefiles in TRACEDIR that the driver
 * will use for testing. Modify this if you want to add or delete
 * traces from the driver's test suite.
 */

#define DEFAULT_TRACEFILES  \
  "syn-array-short.rep",	\
  "syn-struct-short.rep",	\
  "syn-string-short.rep",	\
  "syn-mix-short.rep",	\
  "ngram-fox1.rep", \
  "syn-mix-realloc.rep",	\
  "bdd-aa4.rep", \
  "bdd-aa32.rep", \
  "bdd-ma4.rep", \
  "bdd-nq7.rep", \
  "cbit-abs.rep", \
  "cbit-parity.rep", \
  "cbit-satadd.rep", \
  "cbit-xyz.rep", \
  "ngram-gulliver1.rep", \
  "ngram-gulliver2.rep", \
  "ngram-moby1.rep", \
  "ngram-shake1.rep", \
  "syn-array.rep", \
  "syn-mix.rep", \
  "syn-string.rep", \
  "syn-struct.rep"

/*
 * Programs for measuring reference throughputs
 */
#define REF_DRIVER "./mdriver-ref"


/*
 * Speeds measured relative to a benchmark.  Express thresholds
 * relative to benchmark throughput
 * Students get 0 points for this point or below (ops / sec)
 */
#define MIN_SPEED_RATIO       0.30
/*
 * Students get 0 points for this allocation fraction or below
 */
#define MIN_SPACE       0.25


/* 
 * Students can get more points for building faster allocators, up to
 * this point (in ops / sec)
 */
#define MAX_SPEED_RATIO       0.90

/* 
 * Students can get more points for building more efficient allocators,
 * up to this point (1 is perfect).
 */
#define MAX_SPACE       0.74

 /*
  * This constant determines the contributions of space utilization
  * (UTIL_WEIGHT) and throughput (1 - UTIL_WEIGHT) to the performance
  * index.
  */

#define UTIL_WEIGHT .60

/*
 * Max number of random values written to each allocation 
*/
#define MAXFILL        2048

/*
 * Alignment requirement in bytes (either 4, 8, or 16)
 */
#define ALIGNMENT 16

/*********** Parameters controlling dense memory version of heap ***********/
/*
 * Maximum heap size in bytes
 */
#define MAX_DENSE_HEAP (100*(1<<20))  /* 100 MB */

/*
 * Starting address of the memory allocated for the heap by mmap
 */
#define TRY_DENSE_HEAP_START (void *) 0x800000000


/***************** Parameters for looking up reference throughput *********/
/*
 * Location of information on CPU type 
 */
#define CPU_FILE "/proc/cpuinfo"

/*
 * Key in file (spaces removed)
 */
#define CPU_KEY "modelname"

/*
 * File containing throughputs
 */
#define THROUGHPUT_FILE "./throughputs.txt"

/*
 * Keys for checkpoint vs. regular
 */
#define BENCH_KEY  "regular"

#endif /* __CONFIG_H */

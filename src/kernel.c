/*========================================================================
               Copyright (C) 1996-2002 by Jorn Lind-Nielsen
                            All rights reserved

    Permission is hereby granted, without written agreement and without
    license or royalty fees, to use, reproduce, prepare derivative
    works, distribute, and display this software and its documentation
    for any purpose, provided that (1) the above copyright notice and
    the following two paragraphs appear in all copies of the source code
    and (2) redistributions, including without limitation binaries,
    reproduce these notices in the supporting documentation. Substantial
    modifications to this software may be copyrighted by their authors
    and need not follow the licensing terms described here, provided
    that the new terms are clearly indicated in all files where they apply.

    IN NO EVENT SHALL JORN LIND-NIELSEN, OR DISTRIBUTORS OF THIS
    SOFTWARE BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
    INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS
    SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE AUTHORS OR ANY OF THE
    ABOVE PARTIES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    JORN LIND-NIELSEN SPECIFICALLY DISCLAIM ANY WARRANTIES, INCLUDING,
    BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
    ON AN "AS IS" BASIS, AND THE AUTHORS AND DISTRIBUTORS HAVE NO
    OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
    MODIFICATIONS.
========================================================================*/

/*************************************************************************
  $Header$
  FILE:  kernel.c
  DESCR: implements the bdd kernel functions.
  AUTH:  Jorn Lind
  DATE:  (C) june 1997

  WARNING: Do not use pointers to nodes across makenode calls,
           as makenode may resize/move the nodetable.

*************************************************************************/

/** \file kernel.c
 */
 
#include "config.h"
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <assert.h>

#include "kernel.h"
#include "cache.h"
#include "prime.h"

/*************************************************************************
  Various definitions and global variables
*************************************************************************/

/*=== EXTERNAL VARIABLES FOR PACKAGE USERS =============================*/

/**
 * \ingroup kernel
 * \brief The constant true bdd.
 *
 * This bdd holds the constant true value.
 * 
 * \see bddfalse, bdd_true, bdd_false
 */
const BDD bddtrue=1;                     /* The constant true bdd */

/**
 * \ingroup kernel
 * \brief The constant false bdd.
 *
 * This bdd holds the constant false value.
 * 
 * \see bddtrue, bdd_true, bdd_false
 */
const BDD bddfalse=0;                    /* The constant false bdd */


/*=== INTERNAL DEFINITIONS =============================================*/

/* Min. number of nodes (%) that has to be left after a garbage collect
   unless a resize should be done. */
static int minfreenodes=20;


/*=== GLOBAL KERNEL VARIABLES ==========================================*/

int          bddrunning;            /* Flag - package initialized */
int          bdderrorcond;          /* Some error condition */
int          bddnodesize;           /* Number of allocated nodes */
int          bddmaxnodesize;        /* Maximum allowed number of nodes */
int          bddmaxnodeincrease;    /* Max. # of nodes used to inc. table */
BddNode*     bddnodes;          /* All of the bdd nodes */
int          bddfreepos;        /* First free node */
int          bddfreenum;        /* Number of free nodes */
long int     bddproduced;       /* Number of new nodes ever produced */
int          bddvarnum;         /* Number of defined BDD variables */
int*         bddrefstack;       /* Internal node reference stack */
int*         bddrefstacktop;    /* Internal node reference stack top */
int*         bddvar2level;      /* Variable -> level table */
int*         bddlevel2var;      /* Level -> variable table */
jmp_buf      bddexception;      /* Long-jump point for interrupting calc. */
int          bddresized;        /* Flag indicating a resize of the nodetable */

bddCacheStat bddcachestats;


/*=== PRIVATE KERNEL VARIABLES =========================================*/

static BDD*     bddvarset;             /* Set of defined BDD variables */
static int      gbcollectnum;          /* Number of garbage collections */
static int      cachesize;             /* Size of the operator caches */
static long int gbcclock;              /* Clock ticks used in GBC */
static int      usednodes_nextreorder; /* When to do reorder next time */
static bddinthandler  err_handler;     /* Error handler */
static bddgbchandler  gbc_handler;     /* Garbage collection handler */
static bdd2inthandler resize_handler;  /* Node-table-resize handler */


   /* Strings for all error mesages */
static char *errorstrings[BDD_ERRNUM] =
{ "Out of memory", "Unknown variable", "Value out of range",
  "Unknown BDD root dereferenced", "bdd_init() called twice",
  "File operation failed", "Incorrect file format",
  "Variables not in ascending order", "User called break",
  "Mismatch in size of variable sets",
  "Cannot allocate fewer nodes than already in use",
  "Unknown operator", "Illegal variable set",
  "Bad variable block operation",
  "Trying to decrease the number of variables",
  "Trying to replace with variables already in the bdd",
  "Number of nodes reached user defined maximum",
  "Unknown BDD - was not in node table",
  "Bad size argument",
  "Mismatch in bitvector size",
  "Illegal shift-left/right parameter",
  "Division by zero" };


/*=== OTHER INTERNAL DEFINITIONS =======================================*/

#define NODEHASH(lvl,l,h) (TRIPLE(lvl,l,h) % bddnodesize)


/*************************************************************************
  BDD misc. user operations
*************************************************************************/

/**
 * \ingroup kernel
 * \brief Initializes the bdd package.
 *
 * This function initiates the bdd package and \em must be called before any bdd operations
 * are done. The argument \a nodesize is the initial number of nodes in the nodetable and \a
 * cachesize is the fixed size of the internal caches. Typical values for \a nodesize are 10000
 * nodes for small test examples and up to 1000000 nodes for large examples. A cache size of
 * 10000 seems to work good even for large examples, but lesser values should do it for smaller
 * examples. The number of cache entries can also be set to depend on the size of the nodetable
 * using a call to ::bdd_setcacheratio. The initial number of nodes is not critical for any bdd
 * operation as the table will be resized whenever there are to few nodes left after a garbage
 * collection. But it does have some impact on the efficency of the operations.
 * 
 * \return If no errors occur then 0 is returned, otherwise a negative error code.
 * \see bdd_done, bdd_resize_hook
 */
int bdd_init(int initnodesize, int cs)
{
   int n, err;
   
   srand48( SRAND48SEED ) ;

   if (bddrunning)
      return bdd_error(BDD_RUNNING);
   
   bddnodesize = bdd_prime_gte(initnodesize);
   
   if ((bddnodes=(BddNode*)malloc(sizeof(BddNode)*bddnodesize)) == NULL)
      return bdd_error(BDD_MEMORY);

   bddresized = 0;
   
   for (n=0 ; n<bddnodesize ; n++)
   {
      bddnodes[n].refcou = 0;
      LOW(n) = -1;
      bddnodes[n].hash = 0;
      LEVEL(n) = 0;
      bddnodes[n].next = n+1;
   }
   bddnodes[bddnodesize-1].next = 0;

   bddnodes[0].refcou = bddnodes[1].refcou = MAXREF;
   LOW(0) = HIGH(0) = 0;
   LOW(1) = HIGH(1) = 1;
   
   if ((err=bdd_operator_init(cs)) < 0)
   {
      bdd_done();
      return err;
   }

   bddfreepos = 2;
   bddfreenum = bddnodesize-2;
   bddrunning = 1;
   bddvarnum = 0;
   gbcollectnum = 0;
   gbcclock = 0;
   cachesize = cs;
   usednodes_nextreorder = bddnodesize;
   bddmaxnodeincrease = DEFAULTMAXNODEINC;

   bdderrorcond = 0;
   
   bddcachestats.uniqueAccess = 0;
   bddcachestats.uniqueChain = 0;
   bddcachestats.uniqueHit = 0;
   bddcachestats.uniqueMiss = 0;
   bddcachestats.opHit = 0;
   bddcachestats.opMiss = 0;
   bddcachestats.swapCount = 0;
 
   bdd_gbc_hook(bdd_default_gbchandler);
   bdd_error_hook(bdd_default_errhandler);
   bdd_resize_hook(NULL);
   bdd_pairs_init();
   bdd_reorder_init();
   bdd_fdd_init();
   
   if (setjmp(bddexception) != 0)
      assert(0);

   return 0;
}


/**
 * \ingroup kernel
 * \brief Resets the bdd package.
 *
 * This function frees all memory used by the bdd package and resets the package to it's initial
 * state.
 * 
 * \see bdd_init
 */
void bdd_done(void)
{
   /*sanitycheck(); FIXME */
   bdd_fdd_done();
   bdd_reorder_done();
   bdd_pairs_done();
   
   free(bddnodes);
   free(bddrefstack);
   free(bddvarset);
   free(bddvar2level);
   free(bddlevel2var);
   
   bddnodes = NULL;
   bddrefstack = NULL;
   bddvarset = NULL;
   bddvar2level = NULL;
   bddlevel2var = NULL;

   bdd_operator_done();

   bddrunning = 0;
   bddnodesize = 0;
   bddmaxnodesize = 0;
   bddvarnum = 0;
   bddproduced = 0;
   
   err_handler = NULL;
   gbc_handler = NULL;
   resize_handler = NULL;
}


/**
 * \ingroup kernel
 * \brief Set the number of used bdd variables.
 *
 * This function is used to define the number of variables used in the bdd package. It may be
 * called more than one time, but only to increase the number of variables. The argument \a num
 * is the number of variables to use.
 * 
 * \return Zero on succes, otherwise a negative error code.
 * \see bdd_ithvar, bdd_varnum, bdd_extvarnum
 */
int bdd_setvarnum(int num)
{
   int bdv;
   int oldbddvarnum = bddvarnum;

   bdd_disable_reorder();
      
   if (num < 1  ||  num > MAXVAR)
   {
      bdd_error(BDD_RANGE);
      return bddfalse;
   }

   if (num < bddvarnum)
      return bdd_error(BDD_DECVNUM);
   if (num == bddvarnum)
      return 0;

   if (bddvarset == NULL)
   {
      if ((bddvarset=(BDD*)malloc(sizeof(BDD)*num*2)) == NULL)
	 return bdd_error(BDD_MEMORY);
      if ((bddlevel2var=(int*)malloc(sizeof(int)*(num+1))) == NULL)
      {
	 free(bddvarset);
	 return bdd_error(BDD_MEMORY);
      }
      if ((bddvar2level=(int*)malloc(sizeof(int)*(num+1))) == NULL)
      {
	 free(bddvarset);
	 free(bddlevel2var);
	 return bdd_error(BDD_MEMORY);
      }
   }
   else
   {
      if ((bddvarset=(BDD*)realloc(bddvarset,sizeof(BDD)*num*2)) == NULL)
	 return bdd_error(BDD_MEMORY);
      if ((bddlevel2var=(int*)realloc(bddlevel2var,sizeof(int)*(num+1))) == NULL)
      {
	 free(bddvarset);
	 return bdd_error(BDD_MEMORY);
      }
      if ((bddvar2level=(int*)realloc(bddvar2level,sizeof(int)*(num+1))) == NULL)
      {
	 free(bddvarset);
	 free(bddlevel2var);
	 return bdd_error(BDD_MEMORY);
      }
   }

   if (bddrefstack != NULL)
      free(bddrefstack);
   bddrefstack = bddrefstacktop = (int*)malloc(sizeof(int)*(num*2+4));

   for(bdv=bddvarnum ; bddvarnum < num; bddvarnum++)
   {
      bddvarset[bddvarnum*2] = PUSHREF( bdd_makenode(bddvarnum, 0, 1) );
      bddvarset[bddvarnum*2+1] = bdd_makenode(bddvarnum, 1, 0);
      POPREF(1);
      
      if (bdderrorcond)
      {
	 bddvarnum = bdv;
	 return -bdderrorcond;
      }
      
      bddnodes[bddvarset[bddvarnum*2]].refcou = MAXREF;
      bddnodes[bddvarset[bddvarnum*2+1]].refcou = MAXREF;
      bddlevel2var[bddvarnum] = bddvarnum;
      bddvar2level[bddvarnum] = bddvarnum;
   }

   LEVEL(0) = num;
   LEVEL(1) = num;
   bddvar2level[num] = num;
   bddlevel2var[num] = num;
   
   bdd_pairs_resize(oldbddvarnum, bddvarnum);
   bdd_operator_varresize();
   
   bdd_enable_reorder();
   
   return 0;
}


/**
 * \ingroup kernel
 * \brief Add extra bdd variables.
 *
 * Extends the current number of allocated BDD variables with \a num extra variables.
 * 
 * \return The old number of allocated variables or a negative error code.
 * \see bdd_setvarnum, bdd_ithvar, bdd_nithvar
 */
int bdd_extvarnum(int num)
{
   int start = bddvarnum;
   
   if (num < 0  ||  num > 0x3FFFFFFF)
      return bdd_error(BDD_RANGE);

   bdd_setvarnum(bddvarnum+num);
   return start;
}


/**
 * \ingroup kernel
 * \brief Set a handler for error conditions.
 *
 * Whenever an error occurs in the bdd package a test is done to see if an error handler is
 * supplied by the user and if such exists then it will be called with an error code in the
 * variable \a errcode. The handler may then print any usefull information and return or exit
 * afterwards. This function sets the handler to be \a handler. If a \c NULL argument is
 * supplied then no calls are made when an error occurs. Possible error codes are found in
 * bdd.h. The default handler is ::bdd_default_errhandler which will use \c abort() to
 * terminate the program. Any handler should be defined like this: 
 * \code
 * void my_error_handler(int errcode) { ... } 
 * \endcode
 * 
 * \return The previous handler.
 * \see bdd_errstring
 */
bddinthandler bdd_error_hook(bddinthandler handler)
{
   bddinthandler tmp = err_handler;
   err_handler = handler;
   return tmp;
}


/**
 * \ingroup kernel
 * \brief Clears an error condition in the kernel.
 *
 * The BuDDy kernel may at some point run out of new ROBDD nodes if a maximum limit is set with
 * ::bdd_setmaxnodenum. In this case the current error handler is called and an internal
 * error flag is set. Further calls to BuDDy will always return ::bddfalse. From here BuDDy
 * must either be restarted or ::bdd_clear_error may be called after action is taken to let
 * BuDDy continue. This may not be especially usefull since the default error handler exits
 * the program - other needs may of course exist.
 * 
 * \see bdd_error_hook, bdd_setmaxnodenum
 */
void bdd_clear_error(void)
{
   bdderrorcond = 0;
   bdd_operator_reset();
}


/**
 * \ingroup kernel
 * \brief Set a handler for garbage collections.
 *
 * Whenever a garbage collection is required, a test is done to see if a handler for this event is
 * supplied by the user and if such exists then it is called, both before and after the garbage
 * collection takes places. This is indicated by an integer flag \a pre passed to the handler,
 * which will be one before garbage collection and zero after garbage collection. This
 * function sets the handler to be \a handler. If a \c NULL argument is supplied then no calls are
 * made when a garbage collection takes place. The argument \a pre indicates pre vs. post
 * garbage collection and the argument \a stat contains information about the garbage
 * collection. The default handler is ::bdd_default_gbchandler. Any handler should be
 * defined like this: 
 * \code
 * void my_gbc_handler(int pre, bddGbcStat *stat) { ... } 
 * \endcode
 * 
 * \return The previous handler.
 * \see bdd_resize_hook, bdd_reorder_hook
 */
bddgbchandler bdd_gbc_hook(bddgbchandler handler)
{
   bddgbchandler tmp = gbc_handler;
   gbc_handler = handler;
   return tmp;
}


/**
 * \ingroup kernel
 * \brief Set a handler for nodetable resizes.
 *
 * Whenever it is impossible to get enough free nodes by a garbage collection then the node
 * table is resized and a test is done to see if a handler is supllied by the user for this event. If
 * so then it is called with \a oldsize being the old nodetable size and \a newsize being the new
 * nodetable size. This function sets the handler to be \a handler. If a \c NULL argument is
 * supplied then no calls are made when a table resize is done. No default handler is supplied.
 * Any handler should be defined like this: 
 * \code
 * void my_resize_handler(int * oldsize, int newsize) { ... } 
 * \endcode
 * 
 * \return The previous handler.
 * \see bdd_gbc_hook, bdd_reorder_hook, bdd_setminfreenodes
 */
bdd2inthandler bdd_resize_hook(bdd2inthandler handler)
{
   bdd2inthandler tmp = handler;
   resize_handler = handler;
   return tmp;
}


/**
 * \ingroup kernel
 * \brief Set maximum number of nodes used to increase node table.
 *
 * The node table is expanded by doubling the size of the table when no more free nodes can be
 * found, but a maximum for the number of new nodes added can be set with ::bdd_setmaxincrease to \a
 * size nodes. The default is 50000 nodes (1 Mb).
 * 
 * \return The old threshold on succes, otherwise a negative error code.
 * \see bdd_setmaxnodenum, bdd_setminfreenodes
 */
int bdd_setmaxincrease(int size)
{
   int old = bddmaxnodeincrease;
   
   if (size < 0)
      return bdd_error(BDD_SIZE);

   bddmaxnodeincrease = size;
   return old;
}

/**
 * \ingroup kernel
 * \brief Set the maximum available number of bdd nodes.
 *
 * This function sets the maximal number of bdd nodes the package may allocate before it gives
 * up a bdd operation. The argument \a size is the absolute maximal number of nodes there may be
 * allocated for the nodetable. Any attempt to allocate more nodes results in the constant
 * false being returned and the error handler being called until some nodes are deallocated. A
 * value of 0 is interpreted as an unlimited amount. It is \em not possible to specify fewer
 * nodes than there has already been allocated.
 * 
 * \return The old threshold on success, otherwise a negative error code.
 * \see bdd_setmaxincrease, bdd_setminfreenodes
 */
int bdd_setmaxnodenum(int size)
{
   if (size > bddnodesize  ||  size == 0)
   {
      int old = bddmaxnodesize;
      bddmaxnodesize = size;
      return old;
   }

   return bdd_error(BDD_NODES);
}


/**
 * \ingroup kernel
 * \brief Set minimum number of nodes to be reclaimed after gbc (as a percentage).
 *
 * Whenever a garbage collection is executed the number of free nodes left are checked to see if
 * a resize of the node table is required. 
 * If (::bdd_getnodenum() - ::bdd_getallocnum())*100/::bdd_getallocnum() <= \a mf then a resize is
 * initiated. The range of \a mf is of course \f$0\ldots 100\f$ and has some influence on how fast the
 * package is. A low number means harder attempts to avoid resizing and saves space, and a high
 * number reduces the time used in garbage collections. The default value is 20.
 * 
 * \return The old threshold on success, otherwise a negative error code.
 * \see bdd_setmaxnodenum, bdd_setmaxincrease
 */
int bdd_setminfreenodes(int mf)
{
   int old = minfreenodes;
   
   if (mf<0 || mf>100)
      return bdd_error(BDD_RANGE);

   minfreenodes = mf;
   return old;
}


/**
 * \ingroup kernel
 * \brief Get the number of active nodes in use.
 *
 * Returns the number of nodes in the nodetable that are currently in use. Note that dead nodes
 * that have not been reclaimed yet by a garbage collection are counted as active.
 * 
 * \return The number of nodes.
 * \see bdd_getallocnum, bdd_setmaxnodenum
 */
int bdd_getnodenum(void)
{
   return bddnodesize - bddfreenum;
}


/**
 * \ingroup kernel
 * \brief Get the number of allocated nodes.
 *
 * Returns the number of nodes currently allocated. This includes both dead and active nodes.
 * 
 * \return The number of nodes.
 * \see bdd_getnodenum, bdd_setmaxnodenum
 */
int bdd_getallocnum(void)
{
   return bddnodesize;
}


/**
 * \ingroup kernel
 * \brief Test whether the package is started or not.
 *
 * This function tests the internal state of the package and returns a status.
 * 
 * \return 1 (true) if the package has been started, otherwise 0.
 * \see bdd_init, bdd_done
 */
int bdd_isrunning(void)
{
   return bddrunning;
}


/**
 * \ingroup kernel
 * \brief Returns a text string with version information.
 *
 * This function returns a text string with information about the version of the bdd package.
 * 
 * \see bdd_versionnum
 */
char *bdd_versionstr(void)
{
   static char str[] = "BuDDy -  release " PACKAGE_VERSION;
   return str;
}


/**
 * \ingroup kernel
 * \brief Returns the version number of the bdd package.
 *
 * This function returns the version number of the bdd package. The number is in the range 10-99
 * for version 1.0 to 9.9.
 * 
 * \see bdd_versionstr
 */
int bdd_versionnum(void)
{
   return MAJOR_VERSION * 10 + MINOR_VERSION;
}


/**
 * \ingroup kernel
 * \brief Returns some status information about the bdd package.
 *
 * This function acquires information about the internal state of the bdd package. The status
 * information is written into the \a stat argument.
 * 
 * \see bddStat
 */
void bdd_stats(bddStat *s)
{
   s->produced = bddproduced;
   s->nodenum = bddnodesize;
   s->maxnodenum = bddmaxnodesize;
   s->freenodes = bddfreenum;
   s->minfreenodes = minfreenodes;
   s->varnum = bddvarnum;
   s->cachesize = cachesize;
   s->gbcnum = gbcollectnum;
}



/**
 * \ingroup kernel
 * \brief Fetch cache access usage.
 *
 * Fetches cache usage information and stores it in \a s. The fields of \a s can be found in the
 * documentation for ::bddCacheStat. This function may or may not be compiled into the BuDDy
 * package - depending on the setup at compile time of BuDDy.
 * 
 * \see bddCacheStat, bdd_printstat
 */
void bdd_cachestats(bddCacheStat *s)
{
   *s = bddcachestats;
}


/**
 * \ingroup kernel
 * \brief Print cache statistics.
 *
 * Prints information about the cache performance on standard output (or the supplied file).
 * The information contains the number of accesses to the unique node table, the number of
 * times a node was (not) found there and how many times a hash chain had to traversed. Hit and
 * miss count is also given for the operator caches.
 * 
 * \see bddCacheStat, bdd_cachestats
 */
void bdd_fprintstat(FILE *ofile)
{
   bddCacheStat s;
   bdd_cachestats(&s);
   
   fprintf(ofile, "\nCache statistics\n");
   fprintf(ofile, "----------------\n");
   
   fprintf(ofile, "Unique Access:  %ld\n", s.uniqueAccess);
   fprintf(ofile, "Unique Chain:   %ld\n", s.uniqueChain);
   fprintf(ofile, "Unique Hit:     %ld\n", s.uniqueHit);
   fprintf(ofile, "Unique Miss:    %ld\n", s.uniqueMiss);
   fprintf(ofile, "=> Hit rate =   %.2f\n",
	   (s.uniqueHit+s.uniqueMiss > 0) ? 
	   ((float)s.uniqueHit)/((float)s.uniqueHit+s.uniqueMiss) : 0);
   fprintf(ofile, "Operator Hits:  %ld\n", s.opHit);
   fprintf(ofile, "Operator Miss:  %ld\n", s.opMiss);
   fprintf(ofile, "=> Hit rate =   %.2f\n",
	   (s.opHit+s.opMiss > 0) ? 
	   ((float)s.opHit)/((float)s.opHit+s.opMiss) : 0);
   fprintf(ofile, "Swap count =    %ld\n", s.swapCount);
}


void bdd_printstat(void)
{
   bdd_fprintstat(stdout);
}


/*************************************************************************
  Error handler
*************************************************************************/

/**
 * \ingroup kernel
 * \brief Converts an error code to a string.
 *
 * Converts a negative error code \a errorcode to a descriptive string that can be used for
 * error handling.
 * 
 * \return An error description string if \a e is known, otherwise \c NULL.
 * \see bdd_err_hook
 */
const char *bdd_errstring(int e)
{
   e = abs(e);
   if (e<1 || e>BDD_ERRNUM)
      return NULL;
   return errorstrings[e-1];
}


void bdd_default_errhandler(int e)
{
   fprintf(stderr, "BDD error: %s\n", bdd_errstring(e));
   abort();
}


int bdd_error(int e)
{
   if (err_handler != NULL)
      err_handler(e);
   
   return e;
}


/*************************************************************************
  BDD primitives
*************************************************************************/

/**
 * \ingroup kernel
 * \brief Returns the constant true bdd.
 *
 * This function returns the constant true bdd and can freely be used together with the
 * ::bddtrue and ::bddfalse constants.
 * 
 * \return The constant true bdd.
 * \see bdd_false, bddtrue, bddfalse
 */
BDD bdd_true(void)
{
   return 1;
}


/**
 * \ingroup kernel
 * \brief Returns the constant false bdd.
 *
 * This function returns the constant false bdd and can freely be used together with the
 * ::bddtrue and ::bddfalse constants.
 * 
 * \return The constant false bdd.
 * \see bdd_true, bddtrue, bddfalse
 */
BDD bdd_false(void)
{
   return 0;
}


/**
 * \ingroup kernel
 * \brief Returns a bdd representing the i'th variable.
 *
 * This function is used to get a bdd representing the i'th variable (one node with the children
 * true and false). The requested variable must be in the range define by ::bdd_setvarnum
 * starting with 0 being the first. For ease of use then the bdd returned from ::bdd_ithvar does
 * not have to be referenced counted with a call to ::bdd_addref. The initial variable order is
 * defined by the index \a var that also defines the position in the variable order --
 * variables with lower indices are before those with higher indices.
 * 
 * \return The i'th variable on success, otherwise the constant false bdd.
 * \see bdd_setvarnum, bdd_nithvar, bddtrue, bddfalse
 */
BDD bdd_ithvar(int var)
{
   if (var < 0  ||  var >= bddvarnum)
   {
      bdd_error(BDD_VAR);
      return bddfalse;
   }

   return bddvarset[var*2];
}


/**
 * \ingroup kernel
 * \brief Returns a bdd representing the negation of the i'th variable.
 *
 * This function is used to get a bdd representing the negation of the i'th variable (one node
 * with the children false and true). The requested variable must be in the range defined by
 * ::bdd_setvarnum starting with 0 being the first. For ease of use then the bdd returned from
 * ::bdd_nithvar does not have to be referenced counted with a call to ::bdd_addref.
 * 
 * \return The negated i'th variable on success, otherwise the constant false bdd.
 * \see bdd_setvarnum, bdd_ithvar, bddtrue, bddfalse
 */
BDD bdd_nithvar(int var)
{
   if (var < 0  ||  var >= bddvarnum)
   {
      bdd_error(BDD_VAR);
      return bddfalse;
   }
   
   return bddvarset[var*2+1];
}


/**
 * \ingroup kernel
 * \brief Returns the number of defined variables.
 *
 * This function returns the number of variables defined by a call to ::bdd_setvarnum.
 * 
 * \return The number of defined variables.
 * \see bdd_setvarnum, bdd_ithvar
 */
int bdd_varnum(void)
{
   return bddvarnum;
}


/**
 * \ingroup info
 * \brief Gets the variable labeling the bdd.
 *
 * Gets the variable labeling the bdd \a r.
 * 
 * \return The variable number.
 */
int bdd_var(BDD root)
{
   CHECK(root);
   if (root < 2)
      return bdd_error(BDD_ILLBDD);

   return (bddlevel2var[LEVEL(root)]);
}


/**
 * \ingroup info
 * \brief Gets the false branch of a bdd.
 *
 * Gets the false branch of the bdd \a r.
 * 
 * \return The bdd of the false branch.
 * \see bdd_high
 */
BDD bdd_low(BDD root)
{
   CHECK(root);
   if (root < 2)
      return bdd_error(BDD_ILLBDD);

   return (LOW(root));
}


/**
 * \ingroup info
 * \brief Gets the true branch of a bdd.
 *
 * Gets the true branch of the bdd \a r.
 * 
 * \return The bdd of the true branch.
 * \see bdd_low
 */
BDD bdd_high(BDD root)
{
   CHECK(root);
   if (root < 2)
      return bdd_error(BDD_ILLBDD);

   return (HIGH(root));
}



/*************************************************************************
  Garbage collection and node referencing
*************************************************************************/

void bdd_default_gbchandler(int pre, bddGbcStat *s)
{
   if (!pre)
   {
      printf("Garbage collection #%d: %d nodes / %d free",
	     s->num, s->nodes, s->freenodes);
      printf(" / %.1fs / %.1fs total\n",
	     (float)s->time/(float)(CLOCKS_PER_SEC),
	     (float)s->sumtime/(float)CLOCKS_PER_SEC);
   }
}


static void bdd_gbc_rehash(void)
{
   int n;

   bddfreepos = 0;
   bddfreenum = 0;

   for (n=bddnodesize-1 ; n>=2 ; n--)
   {
      register BddNode *node = &bddnodes[n];

      if (LOWp(node) != -1)
      {
	 register unsigned int hash;

	 hash = NODEHASH(LEVELp(node), LOWp(node), HIGHp(node));
	 node->next = bddnodes[hash].hash;
	 bddnodes[hash].hash = n;
      }
      else
      {
	 node->next = bddfreepos;
	 bddfreepos = n;
	 bddfreenum++;
      }
   }
}


void bdd_gbc(void)
{
   int *r;
   int n;
   long int c2, c1 = clock();

   if (gbc_handler != NULL)
   {
      bddGbcStat s;
      s.nodes = bddnodesize;
      s.freenodes = bddfreenum;
      s.time = 0;
      s.sumtime = gbcclock;
      s.num = gbcollectnum;
      gbc_handler(1, &s);
   }
   
   for (r=bddrefstack ; r<bddrefstacktop ; r++)
      bdd_mark(*r);

   for (n=0 ; n<bddnodesize ; n++)
   {
      if (bddnodes[n].refcou > 0)
	 bdd_mark(n);
      bddnodes[n].hash = 0;
   }
   
   bddfreepos = 0;
   bddfreenum = 0;

   for (n=bddnodesize-1 ; n>=2 ; n--)
   {
      register BddNode *node = &bddnodes[n];

      if ((LEVELp(node) & MARKON)  &&  LOWp(node) != -1)
      {
	 register unsigned int hash;

	 LEVELp(node) &= MARKOFF;
	 hash = NODEHASH(LEVELp(node), LOWp(node), HIGHp(node));
	 node->next = bddnodes[hash].hash;
	 bddnodes[hash].hash = n;
      }
      else
      {
	 LOWp(node) = -1;
	 node->next = bddfreepos;
	 bddfreepos = n;
	 bddfreenum++;
      }
   }

   bdd_operator_reset();

   c2 = clock();
   gbcclock += c2-c1;
   gbcollectnum++;

   if (gbc_handler != NULL)
   {
      bddGbcStat s;
      s.nodes = bddnodesize;
      s.freenodes = bddfreenum;
      s.time = c2-c1;
      s.sumtime = gbcclock;
      s.num = gbcollectnum;
      gbc_handler(0, &s);
   }
}


/**
 * \ingroup kernel
 * \brief Increases the reference count on a node.
 *
 * Reference counting is done on externaly referenced nodes only and the count for a specific
 * node \a r can and must be increased using this function to avoid loosing the node in the next
 * garbage collection.
 * 
 * \see bdd_delref
 * \return The BDD node \a r.
 */
BDD bdd_addref(BDD root)
{
   if (root < 2  ||  !bddrunning)
      return root;
   if (root >= bddnodesize)
      return bdd_error(BDD_ILLBDD);
   if (LOW(root) == -1)
      return bdd_error(BDD_ILLBDD);

   INCREF(root);
   return root;
}


/**
 * \ingroup kernel
 * \brief Decreases the reference count on a node.
 *
 * Reference counting is done on externaly referenced nodes only and the count for a specific
 * node \a r can and must be decreased using this function to make it possible to reclaim the node
 * in the next garbage collection.
 * 
 * \see bdd_addref
 * \return The BDD node \a r.
 */
BDD bdd_delref(BDD root)
{
   if (root < 2  ||  !bddrunning)
      return root;
   if (root >= bddnodesize)
      return bdd_error(BDD_ILLBDD);
   if (LOW(root) == -1)
      return bdd_error(BDD_ILLBDD);

   /* if the following line is present, fails there much earlier */ 
   if (!HASREF(root)) bdd_error(BDD_BREAK); /* distinctive */
   
   DECREF(root);
   return root;
}


/*=== RECURSIVE MARK / UNMARK ==========================================*/

void bdd_mark(int i)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];
   if (LEVELp(node) & MARKON  ||  LOWp(node) == -1)
      return;
   
   LEVELp(node) |= MARKON;
   
   bdd_mark(LOWp(node));
   bdd_mark(HIGHp(node));
}


void bdd_mark_upto(int i, int level)
{
   BddNode *node = &bddnodes[i];
   
   if (i < 2)
      return;
   
   if (LEVELp(node) & MARKON  ||  LOWp(node) == -1)
      return;
   
   if (LEVELp(node) > level)
      return;

   LEVELp(node) |= MARKON;

   bdd_mark_upto(LOWp(node), level);
   bdd_mark_upto(HIGHp(node), level);
}


void bdd_markcount(int i, int *cou)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];
   if (MARKEDp(node)  ||  LOWp(node) == -1)
      return;
   
   SETMARKp(node);
   *cou += 1;
   
   bdd_markcount(LOWp(node), cou);
   bdd_markcount(HIGHp(node), cou);
}


void bdd_unmark(int i)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];

   if (!MARKEDp(node)  ||  LOWp(node) == -1)
      return;
   UNMARKp(node);
   
   bdd_unmark(LOWp(node));
   bdd_unmark(HIGHp(node));
}


void bdd_unmark_upto(int i, int level)
{
   BddNode *node = &bddnodes[i];

   if (i < 2)
      return;
   
   if (!(LEVELp(node) & MARKON))
      return;
   
   LEVELp(node) &= MARKOFF;
   
   if (LEVELp(node) > level)
      return;

   bdd_unmark_upto(LOWp(node), level);
   bdd_unmark_upto(HIGHp(node), level);
}


/*************************************************************************
  Unique node table functions
*************************************************************************/

int bdd_makenode(unsigned int level, int low, int high)
{
   register BddNode *node;
   register unsigned int hash;
   register int res;

#ifdef CACHESTATS
   bddcachestats.uniqueAccess++;
#endif
   
      /* check whether childs are equal */
   if (low == high)
      return low;

      /* Try to find an existing node of this kind */
   hash = NODEHASH(level, low, high);
   res = bddnodes[hash].hash;

   while(res != 0)
   {
      if (LEVEL(res) == level  &&  LOW(res) == low  &&  HIGH(res) == high)
      {
#ifdef CACHESTATS
	 bddcachestats.uniqueHit++;
#endif
	 return res;
      }

      res = bddnodes[res].next;
#ifdef CACHESTATS
      bddcachestats.uniqueChain++;
#endif
   }
   
      /* No existing node -> build one */
#ifdef CACHESTATS
   bddcachestats.uniqueMiss++;
#endif

      /* Any free nodes to use ? */
   if (bddfreepos == 0)
   {
      if (bdderrorcond)
	 return 0;
      
         /* Try to allocate more nodes */
      bdd_gbc();

      if ((bddnodesize-bddfreenum) >= usednodes_nextreorder  &&
	   bdd_reorder_ready())
      {
	 longjmp(bddexception,1);
      }

      if ((bddfreenum*100) / bddnodesize <= minfreenodes)
      {
	 bdd_noderesize(1);
	 hash = NODEHASH(level, low, high);
      }

         /* Panic if that is not possible */
      if (bddfreepos == 0)
      {
	 bdd_error(BDD_NODENUM);
	 bdderrorcond = abs(BDD_NODENUM);
	 return 0;
      }
   }

      /* Build new node */
   res = bddfreepos;
   bddfreepos = bddnodes[bddfreepos].next;
   bddfreenum--;
   bddproduced++;
   
   node = &bddnodes[res];
   LEVELp(node) = level;
   LOWp(node) = low;
   HIGHp(node) = high;
   
      /* Insert node */
   node->next = bddnodes[hash].hash;
   bddnodes[hash].hash = res;

   return res;
}


int bdd_noderesize(int doRehash)
{
   BddNode *newnodes;
   int oldsize = bddnodesize;
   int n;

   if (bddnodesize >= bddmaxnodesize  &&  bddmaxnodesize > 0)
      return -1;
   
   bddnodesize = bddnodesize << 1;

   if (bddnodesize > oldsize + bddmaxnodeincrease)
      bddnodesize = oldsize + bddmaxnodeincrease;

   if (bddnodesize > bddmaxnodesize  &&  bddmaxnodesize > 0)
      bddnodesize = bddmaxnodesize;

   bddnodesize = bdd_prime_lte(bddnodesize);
   
   if (resize_handler != NULL)
      resize_handler(oldsize, bddnodesize);

   newnodes = (BddNode*)realloc(bddnodes, sizeof(BddNode)*bddnodesize);
   if (newnodes == NULL)
      return bdd_error(BDD_MEMORY);
   bddnodes = newnodes;

   if (doRehash)
      for (n=0 ; n<oldsize ; n++)
	 bddnodes[n].hash = 0;
   
   for (n=oldsize ; n<bddnodesize ; n++)
   {
      bddnodes[n].refcou = 0;
      bddnodes[n].hash = 0;
      LEVEL(n) = 0;
      LOW(n) = -1;
      bddnodes[n].next = n+1;
   }
   bddnodes[bddnodesize-1].next = bddfreepos;
   bddfreepos = oldsize;
   bddfreenum += bddnodesize - oldsize;

   if (doRehash)
      bdd_gbc_rehash();

   bddresized = 1;
   
   return 0;
}


void bdd_checkreorder(void)
{
   bdd_reorder_auto();

      /* Do not reorder before twice as many nodes have been used */
   usednodes_nextreorder = 2 * (bddnodesize - bddfreenum);
   
      /* And if very little was gained this time (< 20%) then wait until
       * even more nodes (upto twice as many again) have been used */
   if (bdd_reorder_gain() < 20)
      usednodes_nextreorder +=
	 (usednodes_nextreorder * (20-bdd_reorder_gain())) / 20;
}


/*************************************************************************
  Variable sets
*************************************************************************/

/**
 * \ingroup kernel
 * \brief Returns an integer representation of a variable set.
 *
 * Scans a variable set \a r and copies the stored variables into an integer array of variable
 * numbers. The argument \a varset is the address of an integer pointer where the array is stored and
 * \a varnum is a pointer to an integer where the number of elements are stored. It is the user's
 * responsibility to make sure the array is deallocated by a call to \c free(v). The numbers
 * returned are guaranteed to be in ascending order.
 * 
 * \see bdd_makeset
 * \return Zero on success, otherwise a negative error code.
 */
int bdd_scanset(BDD r, int **varset, int *varnum)
{
   int n, num;

   CHECK(r);
   if (r < 2)
   {
      *varnum = 0;
      *varset = NULL;
      return 0;
   }
   
   for (n=r, num=0 ; n > 1 ; n=HIGH(n))
      num++;

   if (((*varset) = (int *)malloc(sizeof(int)*num)) == NULL)
      return bdd_error(BDD_MEMORY);
   
   for (n=r, num=0 ; n > 1 ; n=HIGH(n))
      (*varset)[num++] = bddlevel2var[LEVEL(n)];

   *varnum = num;

   return 0;
}


/**
 * \ingroup kernel
 * \brief Builds a bdd variable set from an integer array.
 *
 * Reads a set of variable numbers from the integer array \a varset which must hold exactly \a varnum
 * integers and then builds a BDD representing the variable set. The BDD variable set is
 * represented as the conjunction of all the variables in their positive form and may just as
 * well be made that way by the user. The user should keep a reference to the returned BDD instead
 * of building it every time the set is needed.
 * 
 * \see bdd_scanset
 * \return A BDD variable set.
 */
BDD bdd_makeset(int *varset, int varnum)
{
   int v, res=1;
   
   for (v=varnum-1 ; v>=0 ; v--)
   {
      BDD tmp;
      bdd_addref(res);
      tmp = bdd_apply(res, bdd_ithvar(varset[v]), bddop_and);
      bdd_delref(res);
      res = tmp;
   }

   return res;
}


/* EOF */

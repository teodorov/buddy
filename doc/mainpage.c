/**
 * \defgroup info info
 * \defgroup kernel kernel
 * \defgroup fdd fdd
 * \defgroup bvec bvec
 * \defgroup fileio fileio
 * \defgroup operator operator
 *
 * \mainpage BuDDy: A BDD package
 * \section section0 Programming with BuDDy 
 * First of all a program needs to call 
 * \verbatim
 * bdd_init(nodenum,cachesize)
 * \endverbatim
 * to initialize the BDD package. The \a nodenum parameter sets the initial number of BDD nodes and 
 * \a cachesize sets the size of the caches used for the BDD operators (not the
 * unique node table). These caches are used for ::bdd_apply among others.
 *
 * Good initial values are
 *  - Small test examples: \a nodenum = 1000, \a cachesize = 100
 *  - Small examples: \a nodenum = 10000, \a cachesize =1000
 *  - Medium sized examples: \a nodenum = 100000, \a cachesize = 10000
 *  - Large examples: \a nodenum = 1000000, \a cachesize = variable
 *
 * Too few nodes will only result in reduced performance as this
 * increases the number of garbage collections needed. If the package
 * needs more nodes, then it will automatically increase the size of the
 * node table.  Use ::bdd_setminfreenodes to change the parameters
 * for when this is done and use ::bdd_setcacheratio to enable
 * dynamical resizing of the operator caches. You may also use the
 * function ::bdd_setmaxincrease to adjust how BuDDy resizes the
 * node table.
 *
 * After the initialization a call must be done to ::bdd_setvarnum
 * to define how many variables to use in this session. This number may
 * be increased later on either by calls to ::bdd_setvarnum or to
 * ::bdd_extvarnum.
 *
 * The atomic functions for getting new BDD nodes are 
 * ::bdd_ithvar(i) and ::bdd_nithvar(i) which return references
 * to BDD nodes of the form \f$(v_i,0,1)\f$ and \f$(v_i,1,0)\f$. The nodes
 * constructed in this way correspond to the positive and negative
 * versions of a single variable.  Initially the variable order is \f$v_0 <
 * v_1 < \ldots < v_{n-1} < v_n\f$.
 *   
 * The BDDs returned from ::bdd_ithvar can then be used to form
 * new BDDs by calling ::bdd_apply(a,b,op) where \a op may be
 * ::bddop_and or any of the other operators defined in ::bdd.h.
 * The apply function performs the binary operation indicated by 
 * \a op. Use ::bdd_not to negate a BDD.  The result from 
 * ::bdd_apply and any other BDD operator \a must be handed over to
 * ::bdd_addref to increase the reference count of the node before
 * any other operation is performed.  This is done to prevent the BDD
 * from being garbage collected. When a BDD is no longer in use, it can
 * be de-referenced by a call to ::bdd_delref.  The exceptions to
 * this are the return values from ::bdd_ithvar and
 * ::bdd_nithvar. These do not need to be reference counted, although
 * it is not an error to do so. The use of the BDD package ends with a
 * call to ::bdd_done. See below for an example.
 *
 * \verbatim
 * #include <bdd.h>
 *
 * main(void)
 * {
 *    bdd x,y,z;
 *
 *    bdd_init(1000,100);
 *    bdd_setvarnum(5);
 *
 *    x = bdd_ithvar(0);
 *    y = bdd_ithvar(1);
 *    z = bdd_addref(bdd_apply(x,y,bddop_and));
 *
 *    bdd_printtable(z);
 *    bdd_delref(z);
 *    bdd_done();
 * }
 * \endverbatim
 * Standard C interface to BuDDy. In this mode both ::bdd and
 * ::BDD can be used as BuDDy BDD types. The C interface requires the
 * user to ensure garbage collection is handled correctly. This means
 * calling ::bdd_addref every time a new BDD is created, and
 * ::bdd_delref whenever a BDD is not in use anymore.
 *
 * \verbatim
 * #include <bdd.h>
 *
 * main(void)
 * {
 *    bdd x,y,z;
 *
 *    bdd_init(1000,100);
 *    bdd_setvarnum(5);
 *
 *    x = bdd_ithvar(0);
 *    y = bdd_ithvar(1);
 *    z = x & y;
 *
 *    cout << bddtable << z << endl;
 *
 *    bdd_done();
 * }
 * \endverbatim
 * C++ interface to BuDDy. In this mode 'bdd' is a C++ class
 * that wraps a handler around the standard C interface, and the
 * 'BDD' type referes to the standard C BDD type. The C++ interface
 * handles all garbage collection, so no calls to ::bdd_addref and
 * ::bdd_delref are needed.
 *
 * Information on the BDDs can be found using the ::bdd_var,
 * ::bdd_low and ::bdd_high functions that returns the variable
 * labelling a BDD, the low branch and the high branch of a BDD.
 *
 * Printing BDDs is done using the functions ::bdd_printall that
 * prints \a all used nodes, ::bdd_printtable that prints the
 * part of the nodetable that corresponds to a specific BDD and
 * :bdd_printset that prints a specific BDD as a list of elements in
 * a set (all paths ending in the true terminal).

 * \subsection  More Examples

 * More complex examples can be found in the ::buddy/examples directory.

 * \section section1 Variable sets

 * For some functions like ::bdd_exist it is possible to pass a
 * whole set of variables to be quantified, using BDDs that represent the
 * variables. These BDDs are simply the conjunction of all the variables
 * in their positive form and can either be build that way or by a call
 * to ::bdd_makeset. For the ::bdd_restrict function the
 * variables need to be included in both positive and negative form which
 * can only be done manually.

 * If for example variable 1 and variable 3 are to be included in a set,
 * then it can be done in two ways, as shown below.
 *
 * \verbatim
 * #include <bdd.h>

 * main()
 * {
 *    bdd v1, v3;
 *    bdd seta, setb;
 *    static int v[2] = {1,3};
 *    
 *    bdd_init(100,100);
 *    bdd_setvarnum(5);
 *
 *    v1 = bdd_ithvar(1);
 *    v3 = bdd_ithvar(3);
 *
 *       /* One way */
 *    seta = bdd_addref( bdd_apply(v1,v3,bddop_and) );
 *    bdd_printtable(seta);
 *
 *       /* Another way */
 *    setb = bdd_addref( bdd_makeset(v,2) );
 *    bdd_printtable(setb);
 * }
 * \endverbatim
 * Two ways to create a variable set.

 * \section section2 Dynamic Variable Reordering
 * \verbatim
 * \begin{figure}
 *   \begin{center}
 *     \input{varblock.pstex_t}
 *     \caption{The variable tree for the variable blocks $v_0\ldots v_9$,
 *       $v_1\ldots v_8$, $v_1\ldots v_4$, $v_5\ldots v_8$, $v_1$, $v_2$,
 *       $v_3$ and $v_4$.}
 *     \label{fig:vartree}
 *   \end{center}
 * \end{figure}
 * \endverbatim

 * Dynamic variable reordering can be done using the functions 
 * ::bdd_reorder(int method) and ::bdd_autoreorder(int method).
 * Where the parameter \a method, for instance can be
 * ::BDD_REORDER_WIN2ITE. The package must know how the BDD variables
 * are related to each other, so the user must define blocks of BDD
 * variables, using ::bdd_addvarblock(bdd var, int fixed). A block
 * is a range of BDD variables that should be kept together. It may
 * either be a simple contiguous sequence of variables or a sequence of
 * other blocks with ranges inside their parents range. In this way all
 * the blocks form a tree of ranges. Partially overlapping blocks are not
 * allowed.

 * Example: Assume the block \f$v_0\ldots v_9\f$, is added as the first block
 * and then the block \f$v_1\ldots v_8\f$. This yields the \f$v_0\ldots v_9\f$
 * block at the top, with the \f$v_1\ldots v_8\f$ block as a child. If now
 * the block \f$v_1\ldots v_4\f$ was added, it would become a child of the
 * \f$v_1\ldots v_8\f$ block, similarly the block \f$v_5\ldots v_8\f$ would be a
 * child of the \f$v_1\ldots v_8\f$ block. If we add the variables \f$v_1\f$,
 * \f$v_2\f$, \f$v_3\f$ and \f$v_4\f$ as single variable blocks we at last get tree
 * showed in figure ref fig:vartree. If all variables should be added
 * as single variable blocks then ::bdd_varblockall can be used
 * instead of doing it manually.

 * The reordering algorithm is then to first reorder the top most blocks
 * and there after descend into each block and reorder these recursively,
 * unless the block is defined as a fixed block.

 * If the user want to control the swapping of variables himself, then
 * the functions ::bdd_swapvar, ::bdd_setvarorder may be used.
 * But this is not possible in conjunction with the use of variable
 * blocks and the ::bdd_swapvar is unfortunately quite slow since a
 * full scan of all the nodes must be done both before and after the
 * swap. Other reordering functions are ::bdd_autoreorder_times,
 * ::bdd_reorder_verbose, ::bdd_sizeprobe_hook and ::bdd_reorder_hook.

 * \section section3 Error Handling

 * If an error occurs then a check is done to see if there is any error
 * handler defined and if so it is called with the error code of
 * interest. The default error handler prints an error message on
 * \a stderr and then aborts the program. A handler can also be defined
 * by the user with a call to ::bdd_error_hook.
 *   
 *   
 * \section section4 The C++ interface

 * Mostly this consists of a set of overloaded function wrappers that
 * takes a ::bdd class and calls the appropriate C functions with the
 * root number stored in the ::bdd class. The names of these wrappers
 * are exactly the same as for the C functions. In addition to this a lot
 * of the C++ operators like | \& - = == are overloaded in order
 * to perform most of the ::bdd_apply() operations. These are listed
 * together with ::bdd_apply. The rest are

 * \verbatim
 *      Operator Description Return value
 *      =        assignment 
 *      ==       test        returns 1 if two BDDs are equal, otherwise 0 
 *      !=       test        returns 0 if two BDDs are equal, otherwise 1 
 *      bdd.id() identity    returns the root number of the BDD 
 * \endverbatim

 * The default constructor for the ::bdd class initializes
 * the bdds to the constant false value.  Reference counting is totally
 * automatic when the ::bdd class is used, here the constructors and
 * destructors takes care of \a all reference counting!  The C++
 * interface is also defined in ::bdd.h so nothing extra is needed to
 * use it.

 * \section section5 Finite Domain Blocks

 * Included in the BDD package is a set of functions for manipulating
 * values of finite domains, like for example finite state machines.
 * These functions are used to allocate blocks of BDD variables to
 * represent integer values instead of only true and false.

 * New finite domain blocks are allocated using ::fdd_extdomain and
 * BDDs representing integer values can be build using ::fdd_ithvar.
 * The BDD representing identity between two sets of different domains
 * can be build using ::fdd_equals. BDDs representing finite domain
 * sets can be printed using ::fdd_printset and the overloaded C++
 * operator ::<<. Pairs for ::bdd_replace can be made using 
 * ::fdd_setpair and variable sets can be made using ::fdd_ithset
 * and ::fdd_makeset. The finite domain block interface is defined
 * for both C and C++. To use this interface you must include ::fdd.h.

 * Encoding using FDDs are done with the Least Significant Bits first in
 * the ordering (top of the BDD). Assume variables \f$V_0 \ldots V_3\f$ are
 * used to encode the value \f$12\f$ - this would yield \f$V_0=0 , V_1=0 ,
 * V_2=1 , V_3=1\f$.

 * An example program using the FDD interface can be found in the
 * examples directory.

 * \section section6 Boolean Vectors

 * Another interface layer for BuDDy implements
 * boolean vectors for use with integer arithmetics. A boolean vector is
 * simply an array of BDDs where each BDD represents one bit of an
 * expression. To use this interface you must include ::bvec.h. As
 * an example, suppose we want to express the following assignment from
 * an expression
 * \f[
 *   x := y + 10
 * \f]
 * what we do is to encode the variable \f$y\f$ and the
 * value \f$10\f$ as boolean vectors \f$y\f$ and \f$v\f$ of a fixed length. Assume we
 * use four bits with LSB to the right, then we get
 * \f[
 *   y = \langle y_4, \ldots, y_1 \rangle
 * \f]
 * \f[
 *   v = \langle 1,0,1,0 \rangle
 * \f]
 * where each \f$y_i\f$ is the BDD variable used to encode the integer
 * variable \f$y\f$. Now the result of the addition can be expressed as the
 * vector \f$z = \langle z_4, \ldots, z_1\rangle \f$ where each \f$z_i\f$ is:
 * \f[
 *   z_i = y_i\ \mbox{xor}\ v_i\ \mbox{xor}\ c_{i-1}
 * \f]
 * and the carry in \f$c_i\f$ is
 * \f[
 *   c_i = (y_i\ \mbox{and}\ v_i)\ \mbox{or}\ (c_{i-1}\ \mbox{and}
 *         \ (y_i\ \mbox{or}\ v_i)).
 * \f]
 * with \f$c_0\f$ = 0. What is left now is to assign the result to \f$x\f$. This
 * is a conjunction of a biimplication of each element in the vectors, so
 * the result is
 * \f[
 *   R = \bigwedge_{i=1}^4 x_i \Leftrightarrow z_i.
 * \f]
 * The above example could be carried out with the following C++ program
 * that utilizes the FDD interface for printing the result.
 * \verbatim
 * #include "bvec.h"

 * main()
 * {
 *    int domain[2] = {16,16};

 *    bdd_init(100,100);
 *    fdd_extdomain(domain, 2);

 *    bvec y = bvec_varfdd(0);
 *    bvec v = bvec_con(4, 10);
 *    bvec z = bvec_add(y, v);

 *    bvec x = bvec_varfdd(1);
 *    bdd  result = bddtrue;
 *    
 *    for (int n=0 ; n<x.bitnum() ; n++)
 *       result &= bdd_apply(x[n], z[n], bddop_biimp);

 *    cout << fddset << result << endl << endl;
 * }
 * \endverbatim

 * The relational operators \f$<,>,\leq,\geq,=,\neq\f$ can also be
 * encoded. Assume we want to encode \f$x \leq y\f$ using the same
 * variables as in the above example. This would be done as:
 * \verbatim
 * #include "bvec.h"

 * main()
 * {
 *    int domain[2] = {16,16};

 *    bdd_init(100,100);
 *    fdd_extdomain(domain, 2);

 *    bvec y = bvec_varfdd(1);
 *    bvec x = bvec_varfdd(0);

 *    bdd  result = bvec_lte(x,y);

 *    cout << fddset << result << endl << endl;
 * }
 * \endverbatim}
 
 * Please note that all vectors that are returned from any of the 
 * bvec_xxx functions are referenced counted by the system.

 * \subsection C++ Interface

 * The C++ interface defines the class
 * \verbatim
 * class bvec
 * {
 *  public:

 *    bvec(void);
 *    bvec(int bitnum);
 *    bvec(int bitnum, int val);
 *    bvec(const bvec &v);
 *    ~bvec(void);

 *    void set(int i, const bdd &b);
 *    bdd operator[](int i)  const;
 *    int bitnum(void) const;
 *    int empty(void) const;
 *    bvec operator=(const bvec &src);
 * }   
 * \endverbatim

 * The default constructor makes an empty vector with no elements, the
 * integer constructor creates a vector with ::bitnum elements (all
 * set to false) and the third constructor creates a vector with
 * \a bitnum elements and assigns the integer value \a val to the
 * vector. Reference counting is done automatically. The i'th element in
 * the vector can be changed with \a set and read with
 * \a operator[]. The number of bits can be found with \a bitnum and
 * the method \a empty returns true if the vector is a NULL vector.

  * \section section7 Efficiency Concerns

 * Getting the most out of any BDD package is not always easy. It
 * requires some knowledge about the optimal order of the BDD variables
 * and it also helps if you have some knowledge of the internals of the
 * package.

 * First of all --- a good initial variable order is a must. Using the
 * automatic reordering methods may be an easy solution, but without a
 * good initial order it may also be a waste of time.

 * Second --- memory is speed. If you allocate as much memory as possible
 * from the very beginning, then BuDDy does not have to waste time trying to
 * allocate more whenever it is needed. So if you really want speed then
 * ::bdd_init should be called with as many nodes as possible. This
 * does unfortunately have the side effect that variable reordering
 * becomes extremely slow since it has to reorder an enormous amount of
 * nodes the first time it is triggered.

 * Third --- the operator caches should be as big as possible. Use the
 * function ::bdd_setcacheratio to make sure the size of these is
 * increased whenever more nodes are allocated. Please note that
 * BuDDy uses a fixed number of elements for these caches as default.
 * You must call ::bdd_setcacheratio to change this. I have found a
 * cache ratio of 1:64 fitting for BDDs of more than one million nodes
 * (the solitare example). This may be a bit overkill, but it works.

 * Fourth --- BuDDy allocates by default a maximum of 50000 nodes (1Mb
 * RAM) every time it resizes the node table. If your problem needs
 * millions of nodes, then this is way too small a number. Use 
 * ::bdd_setmaxincrease to increase this number. In the solitare
 * example something like 5000000 nodes seems more reasonable.

 * Fifth --- by default, BuDDy increases the node table whenever there is
 * less than 20% nodes free. By increasing this value you can make BuDDy
 * go faster and use more memory or vice versa. You can change the value
 * with ::bdd_setminfreenodes.

 * So, to sum it up: if you want speed, then allocate as many nodes as
 * possible, use small cache ratios and set \a maxincrease. If you
 * need memory, then allocate a small number of nodes from the beginning,
 * use a fixed size cache, do not change \a maxincrease and lower 
 * \a minfreenodes.

 * \section section8 Some Implementation details

 * - Negated pointers are not used.

 * - All nodes are stored in one big contiguous array which is also used
 *   as the hash table for finding identical nodes.
 *   
 * - The hash function used to find identical nodes from the triple
 *   \f$(level, low, high)\f$ spreads all nodes evenly in the table. This means
 *   the average length of a hash chain is at most 1.
 *   
 * - Each node in the node table contains a reference count, the
 *   \a level of the variable (this is its position in the current
 *   variable order), the \a high and \a low part, a \a hash
 *   index used to find the first node in a hash chain and a \a next
 *   index used to link the hash chains. Each node fits into 20 bytes of
 *   memory. Other packages uses only 16 bytes for each node but in
 *   addition to this they must keep separate tables with hash table
 *   entries. The effect of this is that the total memory consumption is
 *   20 bytes for each node on average.

 * - Reference counting are done on the externally referenced nodes only.

 * - The ANSI-C ::bdd type is an integer number referring to an
 *   index in the node table. In C++ it is a class.
 *   
 * - New nodes are created by doubling (or just extending) the node
 *   table, not by adding new blocks of nodes.

 * - Garbage collection recursively marks all nodes reachable from the
 *   externally referenced nodes before dead nodes are removed.

 * - Reordering interrupts the current BDD operation and restarts it
 *   again afterwards.
 *   
 * - Reordering changes the hash function to one where all nodes of a
 *   specific level is placed in one continuous block and updates the reference
 *   count field to include all recursive dependencies. After reordering
 *   the package returns to the normal hash function.
 *  
 */

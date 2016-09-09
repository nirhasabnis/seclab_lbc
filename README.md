==================================
LIGHT-WEIGHT BOUNDS CHECKING (LBC)
==================================

LBC is a light-weight bounds checking compiler that instruments 
C programs with runtime checks to ensure that no out-of-bounds sequential 
access is performed.

Copyright (C) 2008 - 2012 by Ashish Misra, Niranjan Hasabnis,
and R.Sekar in Secure Systems Lab, Stony Brook University, 
Stony Brook, NY 11794.

This program is free software; you can redistribute it and/or modify 
it under the terms of the GNU General Public License as published by 
the Free Software Foundation; either version 2 of the License, or 
(at your option) any later version. 

This program is distributed in the hope that it will be useful, 
but WITHOUT ANY WARRANTY; without even the implied warranty of 
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the 
GNU General Public License for more details. 

You should have received a copy of the GNU General Public License 
along with this program; if not, write to the Free Software 
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.

----------------------
1. DIRECTORY STRUCTURE
----------------------

docs/   The docs directory contains the paper published as a research outcome of 
        this project.

include/ This directory contains the header files for LBC.

install/
        This directory contains all important information about compilation and
        installation of various components of LBC.

lib/    This directory contains the code for 2 components: libzcheck, the runtime
        support library for LBC, and LBC's implementation for heap-management
        libc functions.
lib/libzcheck
        This directory contains the code for the runtime support library for
        LBC.
lib/glibc
        This directory contains the code for LBC's implementation for
        heap-management functions. It is implemented as a part of glibc by
        modifying the glibc's code for heap management.

src/    This directory contains OCaml code of LBC that transforms and
        instruments input C program. It operates as a plugin to CIL:
        Infrastructure for C Program Analysis and Transformation.
src/ccured_agressive
        This directory contains the original version of CCured source code.
        Since CCured operates in whole-program analysis mode, it makes some
        aggressive default assumptions such as default type of a pointer is SAFE,
        unless it is inferred otherwise. These assumptions are sound in the
        context of whole-program analysis. But LBC also supports separate
        compilation mode where such aggressive assumptions are unsound.
        That is why LBC also provides conservative version of CCured source code
        where a pointer is WILD, unless it is inferred otherwise.
src/ccured_conservative
        This directory contains the conservative version of CCured source code
        to be used in separate compilation mode. By default, LBC uses aggressive
        version of CCured, but when LBC is to be used in separate compilation
        mode, the user needs to use conservative version of CCured.

usage/  This directory contains files that are required in order to use LBC.

--------------------------------------------------------------
2. SUPPORTED SYSTEMS & REQUIRED VERSIONS OF DEPENDANT SOFTWARE
--------------------------------------------------------------

Currently, LBC is supported for 32-bit versions of Linux running on x86. We
are working on 64-bit version of LBC and would launch it soon.

As far as versions of dependent software are concerned, LBC supports all
versions of CIL (1.3.6, 1.3.7, and 1.4.0), and 2 versions of glibc (2.10.1 and
2.14).

glibc-2.10.1 requires older version of binutils for compilation. This version of
glibc is appropriate for older systems, such as Ubuntu 10.04 or previous. 
Newer versions of the systems, such as Ubuntu 10.10 or recent, support recent
versions of binutils which are needed to compile glibc-2.14. As a result, it is
recommended that recent versions of the systems use glibc-2.14 for compilation
with LBC.

--------------
3. COMPILATION
--------------

Compilation for LBC is divided into 3 parts.
1. Compiling zcheck with CIL
   This step utilizes LBC's OCaml code that transforms potentially dangerous
   object and instruments pointer dereferences to verify their correctness.

2. Compiling glibc with zcheck
   This step utilizes LBC's modified malloc and other heap memory allocation
   functions to compile them into glibc, the GNU libc.

3. Compiling libzcheck
   This last step generates a runtime support library for LBC. The library
   supports functionality for verifying the validity of pointer dereferences,
   and management of guard map.

NOTE:

Some notations used in the compilation steps below:

LBC_TOP: This refers to the place where LBC's source code is unpacked.
GLIBC_TOP: This refers to the place where glibc's source code is unpacked.
CIL_TOP: This refers to the place where CIL's source code is unpacked.

You need to replace these variables with the respective places in your
compilation.

3.1 Compiling zcheck with CIL
-----------------------------

1. First, make sure that you have all the requisite OCaml libraries.
   On Debian linux, Ocaml libraries can be installed using the following command:
    
   "sudo apt-get install ocaml"

2. Download CIL 1.4.0 from http://sourceforge.net/projects/cil/
   NOTE: LBC has also been tested using CIL 1.3.6 and 1.3.7

3. Unpack it using 
   "tar xvfz cil-1.4.0.tar.gz"
   This should create a directory named cil-1.4.0, this is CIL_TOP.

4. Configure cil-1.4.0 by running "CIL_TOP/configure".
   If all pre-requisite OCaml libraries are installed, then ./configure should
   run fine.

5. Now we will apply Makefile patch required to compile zcheck with CIL.
   zcheck is developed as a feature of CIL, but it also requires support from
   CCured analysis and hence its code.

   To apply the patch, 
   - Copy Makefile_1_4_0.patch from <LBC_TOP>/install to <CIL_TOP>.
   - Modify paths to <LBC_TOP>/src in Makefile_1_4_0.patch to the paths where 
     lbc is unpacked. 
   - Run "patch Makefile Makefile_1_4_0.patch"

6. Now "make" and "make install" CIL 1.4.0.
   For more details, please refer http://www.eecs.berkeley.edu/~necula/cil/cil002.html

3.2 Compiling glibc with zcheck
-------------------------------

LBC has been tested with glibc-2.14 and glibc-2.10.1.
The instructions below refer to glibc-2.10.1.
Depending on your system, download glibc from http://www.gnu.org/software/libc/
Refer to section 2 for how to choose between glibc version 2.14 and 2.10.1.

The instructions below assume that glibc-2.10.1 is being installed.

Instructions for compiling glibc:
- Steps below assume that you are in the top level directory of glibc source code
  represented using <GLIBC_TOP>. Replace it using appropriate path where
  glibc-2.10.1 is unpacked.

1. Copy malloc.c, hooks.c, and Versions from <LBC_TOP>/lib/glibc/2.10.1 to
   <GLIBC_TOP>/malloc/.

2. Now to compile glibc,
  - If compiling on Ubuntu, set following environment variable before running configure.

    export CC='gcc -U_FORTIFY_SOURCE -fno-stack-protector' 

    otherwise, you do not need to set CC.

  - Then, invoke configure as follows:

    cd <GLIBC_TOP>/build (If build does not exist, create one.)

    ../configure --with-tls --prefix=`pwd` --without-cvs --enable-add-ons --without-selinux --enable-profile

  - Compile glibc.

    cd <GLIBC_TOP>
    make -C build  (You nay use make's -j option to speed up compilation.)

    make should complete successfully without any error and libc.so should be
    present in build directory.

  - make install -C build


3.3 Compiling libzcheck
-----------------------

In order to compile the runtime support version of LBC, 
  - Enter <LBC_TOP>/lib/libzcheck
  - Type "make"
  - libzcheck.a should have been created.

--------
4. USAGE
--------

LBC can be used in 2 different modes: whole-program analysis mode (merged mode),
and separate compilation mode (non-merged mode). To support these modes, LBC
leverages the functionality provided by CIL. To know more about what these mode
means, one might want to refer to http://www.cs.berkeley.edu/~necula/cil/.

By default, LBC operates in merged mode and utilizes the results of CCured's
analysis to optimize away some runtime verification checks and variable
transformations.

Since LBC can be conceptually thought as a compiler and its runtime
support, we will describe how to use LBC by specifying the required values of
Makefile variables for compilation, i.e., those of CC, CFLAGS, and LDFLAGS.

4.1 Setting Makefile variables
------------------------------

Set these Makefile variables to the values mentioned below:

CC = <CIL_TOP>/bin/cilly     (or the place where cilly is installed)

Append following values to CFLAGS as:
CFLAGS += --keepunused --noRmUnusedInlines --noPrintLn --dooneRet --dozcheck
          --sysDirsFile=<LBC_TOP>/usage/headers.h
          --symbolFile=<LBC_TOP>/usage/symbols.h
          -I<LBC_TOP>/include/

LDFLAGS += -L<LBC_TOP>/lib/libzcheck/ -L<GLIBC_TOP>/build/lib 
           -Xlinker --export-dynamic 
           -Xlinker --rpath=<GLIBC_TOP>/build/lib 
           -Xlinker --dynamic-linker=<GLIBC_TOP>/build/lib/ld-linux.so.2 
           -lc -lzcheck

NOTE:

The list of all the options provided by LBC can be obtained using --help command
for cilly, the CIL driver.

LBC inherits some of the options from CIL. --help command list all such options
also. More details of these options can be found at 
http://www.cs.berkeley.edu/~necula/cil/cil007.html#toc8


4.2 Example
-----------

1) "gcc -g -O2 -Wall foo.c"

   will get transformed to

   "<CIL_TOP>/bin/cilly --keepunused --noRmUnusedInlines --noPrintLn --dooneRet
    --dozcheck --sysDirsFile=<LBC_TOP>/usage/headers.h
    --symbolFile=<LBC_TOP>/usage/symbols.h -g -O2 -Wall -I<LBC_TOP>/include/
    foo.c -L<LBC_TOP>/lib/libzcheck/ -L<GLIBC_TOP>/build/lib -Xlinker --export-dynamic
    -Xlinker --rpath=<GLIBC_TOP>/build/lib -Xlinker
    --dynamic-linker=<GLIBC_TOP>/build/lib/ld-linux.so.2 -lc -lzcheck"

2) "gcc -c -O2 -Wall foo.c"
   "gcc -c -O2 -Wall bar.c"
   "gcc -o main foo.o bar.o -L. -lmylib"

   will get transformed to

   "<CIL_TOP>/bin/cilly --keepunused --noRmUnusedInlines --noPrintLn --dooneRet
    --dozcheck --sysDirsFile=<LBC_TOP>/usage/headers.h
    --symbolFile=<LBC_TOP>/usage/symbols.h -c -O2 -Wall -I<LBC_TOP>/include/
    foo.c"
     
   "<CIL_TOP>/bin/cilly --keepunused --noRmUnusedInlines --noPrintLn --dooneRet
    --dozcheck --sysDirsFile=<LBC_TOP>/usage/headers.h
    --symbolFile=<LBC_TOP>/usage/symbols.h -c -O2 -Wall -I<LBC_TOP>/include/
    bar.c"

   "<CIL_TOP>/bin/cilly --keepunused --noRmUnusedInlines --noPrintLn --dooneRet
    --dozcheck --sysDirsFile=<LBC_TOP>/usage/headers.h
    --symbolFile=<LBC_TOP>/usage/symbols.h -o main -I<LBC_TOP>/include/
    foo.o bar.o -L. -L<LBC_TOP>/lib/libzcheck/ -L<GLIBC_TOP>/build/lib -Xlinker
    --export-dynamic -Xlinker --rpath=<GLIBC_TOP>/build/lib -Xlinker
    --dynamic-linker=<GLIBC_TOP>/build/lib/ld-linux.so.2 -lmylib -lc -lzcheck"


4.3 Using LBC in whole-program analysis mode
--------------------------------------------

To enable whole-program analysis mode, use --merge option provided by CIL. More
details about the merger provided by CIL can be found at
http://www.cs.berkeley.edu/~necula/cil/.

4.4 Using LBC in separate compilation mode
------------------------------------------

To enable separate compilation mode, use --nomerge option provided by CIL.

LBC, by default, performs aggressive static analysis using CCured's results in
whole-program analysis mode. To guarantee soundness, in separate compilation
mode, the analysis needs to be conservative. Before using LBC in separate
compilation mode, user needs to compile LBC with conservative version of CCured.
To do this, make <LBC_TOP>/src/ccured point to
<LBC_TOP>/src/ccured_conservative, and then recompile CIL. When LBC is used in
separate compilation mode, one needs to enable conservative analysis using
--doConservativeAnalysis option provided by LBC.



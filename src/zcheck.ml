(* 
 * LBC is a light-weight bounds checking compiler that instruments 
 * C program with runtime checks to ensure that no out-of-bounds sequential 
 * access is performed.
 * 
 * Copyright (C) 2008 - 2012 by Ashish Misra, Niranjan Hasabnis,
 * and R.Sekar in Secure Systems Lab, Stony Brook University, 
 * Stony Brook, NY 11794.
 * 
 * This program is free software; you can redistribute it and/or modify 
 * it under the terms of the GNU General Public License as published by 
 * the Free Software Foundation; either version 2 of the License, or 
 * (at your option) any later version. 
 * 
 * This program is distributed in the hope that it will be useful, 
 * but WITHOUT ANY WARRANTY; without even the implied warranty of 
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the 
 * GNU General Public License for more details. 
 * 
 * You should have received a copy of the GNU General Public License 
 * along with this program; if not, write to the Free Software 
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.
 *)

(*open Cil*)
open Hashtbl
open Pretty
open Cfg
open Set
open Reachingdefs
open Type
open Ptrnode
open Markptr
open Dataflow
open Cil

(*  This has been picked up from cil.ml +73. 
 *  The basic idea is to get all the machine information (primarily sizeof(long
 *  double))
 *)
module M = Machdep

(* Cil.initCil will set this to the current machine description.
 * Makefile.cil generates the file obj/@ARCHOS@/machdep.ml,
 * which contains the descriptions of gcc and msvc. *)
let theMachine : M.mach ref = ref M.gcc

(*===========================================================================*)
(*  The following section defines all the new exceptions and types used by the
 *  transformation
 *  *)

exception Not_a_Pointer
exception Not_an_Array
exception Incorrect_Input of string

(*  Extremely important. This is the hashtable that we will be using for storing
 *  types. The key point is that this hash will use the TypeSignatures of Cil to
 *  effectively determine the equality of two given types.
 *  Note that the Cil function Cil.typeSig has been used because we want the
 *  attributes to matter. *)
module CTypeHashtbl = 
    Hashtbl.Make 
    (
        struct 
            (*  Note that Cil.typ serves as the key type.   *)
            type t = Cil.typsig

            (*  The key point here is that we will using typesignatures to
             *  compute the equality of types.
             *  This is because type-signature represents the canonical form of
             *  types.  *)
            let equal type1Sig type2Sig =
                (type1Sig = type2Sig)

            (*  Further the hash calculated will be a hash of the typesignature
             *  rather than the type itself.    *)
            let hash (givenTypeSig : typsig) = 
                (Hashtbl.hash givenTypeSig)
        end
    )

(*  The following two types are required to store either an instruction or a
 *  statements to-be-checked expression list. It's a union data-type because at
 *  any point in the CIL processing the expressions being processed can belong
 *  only to either one of them.
 * *)
type instrOrStmt = 
    |   CurrStmt of Cil.stmt
    |   CurrInstr of Cil.instr

(*  This type encodes the fact that we basically have two types of checks,
 *  guardzone checks and array bounds check.
 * *)
type arrayOrPtr =
    (*  The first expression is the lvalue to be checked and the second
     *  expression is the array-bounds.
     *  NOTE: An array check will always be followed by the guardzone check in the exprlist
     *  stored at each statement. This is because when actually evaluating the
     *  checks later, it might turn out that we may not have bounds information
     *  information of the array and hence may have to do a guardzone check after
     *  all.
     *  But the important thing is that when we have an Array entry in the
     *  per-statement expression list, it is guaranteed that the data-type of the
     *  lval was an array.
     * *)
    |   Array of Cil.lval * Cil.exp

    (*  The first exp is basically the pointer used for the dereference operation. 
     *  It does not contain any cast applied after the dereference operation.
     *
     *  The exp is basically the value that needs to be compared against the
     *  guardzone bit sequence. We are forced to follow this approach, because by
     *  applying addressOf and dereferencing operations, the compiler refuses to
     *  directly bring the value into the register at times, directly compares
     *  against the memory. This expression includes the type-cast, because the
     *  compiler brings the data into memory based on the final type.
     *
     *  The third expression is the original value before any type-casting is
     *  done on the dereferenced pointer. This is important because the value of
     *  the dereference depends on the original type. So e.g., you have a char
     *  type cast to an int. Thus the char can have values 127 --  -128. However
     *  you do the comparison based on the final type int. Then you compare
     *  against $0x17171717. The compiler statically figures out this must
     *  result into false and removes the check.
     * *)
    |   Dereference of Cil.exp * Cil.exp * Cil.exp

type exprSourcePair = {source: instrOrStmt ; exprList : arrayOrPtr list }


(*===========================================================================*)
(*  The following section defines all the refs used for switches    *)

(*
 * Whether to use LBC's transformation and instrumentation or not to use it at
 * all. True indicates perform LBC's transformation and instrumentation, false
 * indicates otherwise. *)
let doZCheck = ref false

(*
 * Size of front guard zone size used for global variables.
 * We cannot use variable size front guard zone for global variables
 * because different translation units can have different declarations
 * of the same global variables leading LBC to break on such programs.
 *
 * NOTE: All sizes must be multiple of 8.
 *)
let frontGZSizeGlobal = ref 128

(*
 * Minimum guard zone size for LBC (stack, heap, and global areas). 
 * This can be configured from the command line.
 *)
let minGZSize = ref 8

(*
 * Maximum guard zone size for LBC. 
 * This can also be configured from the command line.
 *)
let maxGZSize = ref 1024

(* 
 * Default guard zone size for LBC. This is used in cases where we cannot use
 * type of the variable to calculate its zone size. E.g., in case of incomplete
 * structures as in C99.
 *)
let defaultGZSize = ref 24

(*  Perform extended checks. It checks if the entire pointer dereference
 *  is clean as compared as to the fast checks where only the first
 *  byte of the pointer dereference is checked  *)
let extendedCheck = ref false

(*  The name of the file that contains a list of symbols(variables) that must be
 *  excluded from transformation    *)
let symbolFile = ref ""
let sysDirsFile = ref ""

(*  The basic idea of this initialization variable is to just check how much
 *  performance impact, the initialization of guardzones of transformed variables
 *  has. Note when this variable is set, there will be no pointer dereference
 *  instrumentation.
 *  *)
let testInit = ref false

(*  The basic idea of this initialization variable is to just check how much
 *  performance impact, ONLY the guardzone checks have on the program WITHOUT
 *  taking into account that variables need to be transformed as well. The
 *  transformation of variable brings in the intangible of memory layout of
 *  program getting affected. Thus when this variable is set there will be no
 *  transformation of variables.
 *  *)
let testInstr = ref false

(*  The basic object here is to instrument ONLY read operations and NOT write
 *  operations. Note that while writing to a memory location, the data is never
 *  brought into a register. Thus our transformation actually introduces a new
 *  memory dereference. This additional dereference is in some sense inevitable. 
 *  This option allows us to remove such dereferences and thus check only the 
 *  truly additional dereferences that we must be able to remove.
 * *)
let instrReadsOnly = ref false

(*  The basic idea behind this initialization variable is to instrument the code
 *  such that we can measure the number of fast guardzone checks versus the number
 *  of bitmap checks that are called.
 *  This will hopefully help in selecting the optimum zone value.
 * *)
let instrMissRate = ref false

(*  The basic idea behind this initialization variable is to indicate that the
 *  only one of the checks (fast pointer check vs slow bitmap check) needs to be
 *  performed. If switch --slow-checks-only is not specified (that is
 *  slowChecksOnly variable is NOT set) then only fast checks are performed
*)
let isolateChecks = ref false

(*  The basic idea behind this initialization variable is to define a macro that
 *  enables calls ONLY to the extensive bitmap checking in the code. Thus it
 *  helps us check the performance impact of just performing slow checks. This
 *  option works ONLY in conjunction with switch --isolate-checks (when variable
 *  isolateChecks variable is set.)
*)
let slowChecksOnly = ref false

(*  The basic idea behind the option is to make sure that the slow checks are
 *  NEVER called. Yet we must also make sure that the compiler does NOT optimize
 *  away the slow check call. This will do by using inline assembly and xoring
 *  the gz_abort_arg with itself and thus making it zero.
 *  Since it's inline assembly, the compiler will not be able to analyze that the
 *  value of gz_abort_arg will always be zero.
 * *)
let testCallImpact = ref false

(*  The list that contains the names of the symbols that must be excluded from
 *  the transformation. It could be because (say) that these symbols belong to
 *  uninstrumented libraries *)
let symbols_list = ref []

(*  The file that contains the list of system directories. Any C function that has 
 *  any of these directories as prefix in its location, will not be
 *  instrumented.
 *  E.g., If the list contains "/usr/include/" then any function that belongs
 *  to the file /usr/include/stddef.h will not be instrumented
 * *)
let sys_dirs_list = ref []

(*  The following variables help us selectively instrument SPECIFIC functions in
 *  the target program. The point of this capability is to be able to study the
 *  behavior of specific functions to the transformation helping to isolate the
 *  reasons of performance impact.
 *  Note that no system functions are permitted to be in the list. Thus, if a
 *  function is present, both in the sys_dir_list header list and this list, then
 *  the function WILL NOT be transformed. 
 * *)
let functionsFile = ref ""
let functions_list = (Hashtbl.create 10)

(*  This option specifies whether the functions mentioned in functionsFile must be exclusively
 *  instrumented OR not instrumented. If set true, then only the specified
 *  functions will be instrumented. Else if set to false, then only those
 *  functions will NOT be instrumented.
 * *)
let doInstrument = ref false

(*  This option specifies whether local variables should be transformed or not.
 * *)
let dontTransformLocals = ref false

(* This option specifies whether to introduce and track bounds for pointers in a function.
 * If set to true, then it doesn't introduce and track bounds for local pointers.
 * If set to false, then it introduces and tracks bounds for local
 * pointers.
 *
 * NOTE: The feature associated with this option is currently not used.
 *)
(*let dontIntroTrackBounds = ref true*)

(*
 * This option disables inter-procedural bounds tracking
 * in which static functions are transformed, if a formal argument
 * is of pointer type. The transformed function
 * has low and high bounds as additional parameter. 
 * The call site is also modified.
 *
 * By default, this is turned off.
 *
 * NOTE: The feature associated with this option is currently not used.
 *)
(*let dontDoInterProcBoundTracking = ref true*)

(* 
 * This option disables the guard-zone and bounds check removal feature
 * based on reaching definition information.
 *
 * By default, this option is set to false.
 *
 * NOTE: The feature associated with this option is currently not used.
 *)
(*let dontEliminateGZChecks = ref true*)

(*
 * This option if set, won't use CCured type analysis to get rid of unnecessary
 * guardzone checks. By default, it is set to true, and thus we don't use CCured
 * type analysis to get rid of unnecessary guardzone checks.
 *)
let dontUseCCuredAnalysis = ref false

(*
 * This option, if set, enables the conservative mode of
 * analysis in which, by default, pointer dereferences
 * are guardzone checked, unless, static analysis figures
 * out that the pointer is used safely.
 *
 * Default value of this option is false.
 *)
let doConservativeAnalysis = ref false

(*
 * Enable the analysis in which we push the initialization of stack variables
 * at the place where it's address is first taken.
 *
 * NOTE: The feature associated with this option is currently not used.
 *)
(*let testInitPush = ref true*)

(*
 * This option if set, disables logging done by zcheck. This is needed to avoid
 * stack overflow exception in the compilation of GCC and perlbmk in SPECINT 2000.
 * The exception occurs because of extra-ordinarily large C files, such as those of size 37K, etc,
 * in GCC and perl.
 *
 * By default, this is disabled as ordinary packages don't have files that are huge.
 *)
let disableLogFileGeneration = ref false

(*
 * The options contains the name of the file which contains the list of
 * functions to be excluded from initialization and uninitialization.
 *)
let iuFunctionsFile = ref ""
let iufunctions_list = ref []

(*===========================================================================*)

(*  Just a set of values to consolidate the names of fields and
 *  variable/type name prefixes used by transformation. Similar to
 *  static consts that we define in C.  *)
let fld_front = "gz_front"
let fld_rear = "gz_rear"
        
let var_name_prefix = "gz_"
let type_name_prefix = "gz_type_"
let var_field_name = "orig_var"
let var_init_suffix = "_init__"

(* NOTE: global variables related to bounds tracking. 
 *       They are disabled as the feature is disabled.
 *
(* _lo is a suffix for a lower bound
 * variable of a given variable.
 *
 * So int* p will have lower bound
 * variable as p_lo.
 *)
let lo_bnd_suffix = "_lo"

(* _hi is a suffix for a upper bound
 * variable of a given variable.
 *
 * So int* p will have upper bound
 * variable as p_hi.
 *)
let hi_bnd_suffix = "_hi"

(*
 * _bnd_trans is a suffix for a function
 * transformed for bound processing
 *)
let trans_func_bnd_suffix = "_bnd_trans"

(*
 * _unsafe is a suffix for a function
 * transformed for safe/unsafe processing
 *)
let trans_func_unsafe_suffix = "_unsafe"

*)

(*  This suffix is specifically used for global pointers to global variables.
 *  Such global pointers are useful in the case of variable declarations that
 *  only have structure declarations instead of structure definitions.
 *  In such cases since the ONLY possible use of original variables is to perform
 *  address-of operation on them, we must use the corresponding dereferenced 
 *  pointers.
 * *)
let global_ptr_suffix = "_ptr"

(*  Init function name suffixes. Note that we have three initialization
 *  functions. 
 *  1.  For array definitions. (i.e., for arrays with sizes and initialization
 *      information)
 *  2.  For array declarations (i.e., for arrays with sizes only)      
 *  3.  Default function for rest of the variables (including pointers and 
 *      array declarations without size information)
 * *)
let suffix_array_defn = "_arr_defn"
let suffix_array_decl = "_arr_decl"
let suffix_ptr_defn = "_ptr_defn"

let suffix_default = "_default"

(*  The name below refers to the name of a temporary variable created in every
 *  function. The objective of the variable is to store the value returned by
 *  the guardzone check functions and then supply it to the abort function.
 * *)
let abort_var_name = "gz_abort_arg"

(*  Note that this variable is NEVER to be used and only serves as a place
 *  holder in the transformationVisitor object.
 * *)
let dummy_global_var = (Cil.makeGlobalVar abort_var_name Cil.uintType)

(*  -------------------------------------------------------------------------   *)
(*  Values for logging *)
let log_dir = "log/"
let log_suffix = ".log"
let log_file_perm = 0o770
let log_width = 80
let log_doc = ref Pretty.nil

(*  The following variable contains the names of memory allocations functions
 *  that we would need to intercept and set the type_size thread-specific
 *  variable before the call to one of these functions    *)
let alloc_funcs = ["malloc"; "memalign"; "posix_memalign"; "realloc"; "valloc"; "pvalloc"]

(*  The basic idea here is to have a tuple of global element name  and header 
 *  file. In the current file being processed, we first check to see if specified 
 *  element present. If it is, then we do NOT include the header file. Else we
 *  do.
 *  Currently we will handle ONLY variable declarations, definitions,
 *  function declarations and typedefs
 *  If more global element types are needed, then we will need to modify the
 *  function process_header_files.
 * *)
let header_file_tuples = [ ]

(*  The variable below denotes the varinfo object for the type_size thread-local
 *  object that we would need to set before the above memory allocation
 *  functions.
 *  *)
let type_size = (Cil.makeVarinfo true "type_size" (TInt(IUInt, [])))

(*  The basic objective of this method is to generate init statements for the
 *  guardzones of a given variable    *)
(*  Note that this value must be synchronized with value in zcheck.h header file
 *)
let zone_value = 0x17171717
let zone_value_exp = Const( CInt64( (Int64.of_int zone_value), IUInt, None) ) 

(*  This value is needed when transforming types whose sizes are less
 *  than 8 bytes or 16 bytes.
 * *)
let const_value_0 = Const(CInt64((Int64.of_int 0), IUInt, None))

(*
 * Table containing info about incomplete types 
 *)
let isInCompleteTypeTbl = (Hashtbl.create 10)

(*
 * This is a hash table containing the mapping between
 * function name and the number of the parameter in it's 
 * prototype which should be checked for Safe/Unsafe.
 * It is used in replacing memory-management functions by
 * their original versions.
 *)
let memMgmtFuncsPtrParamTbl : (string, (int list * string)) Hashtbl.t = (Hashtbl.create 15)

(*
 * This is a hash table containing the mapping between
 * memory management function names and their wrapper
 * names.
 *)
let memMgmtFuncsWrappersTbl : (string, string) Hashtbl.t = (Hashtbl.create 10)

(* 
 * This is hash table maintaining the list of names of untransformed
 * memory allocations functions. It is used for fast lookup.
 *)
let untransformedMemAllocFuncNamesTbl : (string, int) Hashtbl.t = (Hashtbl.create 10)

(*
 * Return a number rounded to next nearest multiple of 8
 *)
let getRoundedSize (size : int) : int =
  if (size > !maxGZSize) then
    !maxGZSize
  else if (size < !minGZSize) then
    !minGZSize
  else
    let quo = (size / 8) in
    let rem = (size mod 8) in
    if(rem = 0) then
      (quo * 8)
    else
      ((quo + 1) * 8)

(* Check if the guard zone size is within
 * the min and max limits. If not, then
 * set it to corresponding bound.
 *)
let checkSizeLimits (size : int) : int =
  if (size < !minGZSize) then
    !minGZSize
  else if (size > !maxGZSize) then
    !maxGZSize
  else
     size

(*
 * Guard zone size selection function
 * Returns the guard zone size rounded to next nearest multiple of 8.
 *)
let getRoundedGZSize (element_size : int) (request_size : int) : int =
  let size = checkSizeLimits (max (2 * element_size) (request_size / 8)) in
    (getRoundedSize size)
    
(*
 * Guard zone size selection function for global variables
 * For globals, we can afford larger guard zones.
 * Returns the guard zone size rounded to next nearest multiple of 8.
 *)
let getRoundedRearGZSizeForGlobal (element_size : int) (request_size : int) : int =
  let size = (max 0 ((max (4 * element_size) (request_size / 8)) -
                                !frontGZSizeGlobal)) 
  in
  let checked_size = checkSizeLimits size in
    (getRoundedSize checked_size)
    
(*===========================================================================*)

(*  This section contains a set of utility methods designed for use by all
 *  classes *)

(*  A set of methods to be used for logging  *)
let log (addLog : doc) : unit =
        log_doc := !log_doc ++ addLog ++ line

let start_method unit = 
        log ((text "    ") ++ align )

let exit_method unit =
        log (line ++ unalign)

(*  This is value that has been defined in the class $CIL/ocamlutil/util.ml +815
 *  and will be useful for us too.  *)
let equals x1 x2 : bool =
    (compare x1 x2) = 0
(*  The compare function used above belongs to (I believe) Pervasives module.   *)

(*
 * Check if the given function name is the one that is specified in 
 * list of functions to be excluded from the initialization and 
 * uninitialization.
 *)

let rec isFuncExcludedFromInitUninit (fname : string) (iufunclist : string
list) : bool =
    let compare_fname (f : string) : bool =
      if (f = fname) then true else false
    in
    List.exists compare_fname iufunclist 

 (*  A little utility method that is needed to create a unique function
 *  name for init function that houses statements that initialize the
 *  guardzones for global variables   
 *)
let validate_name (currName : string) : string =
    begin
        let lower_name = String.uncapitalize currName
        and mod_string (testString : string) : string =
            begin
                let count = ref 0
                and valid_char (currChar : char) : bool =                
                        match currChar with
                        |   'a' ..'z' | 'A' .. 'Z' | '0' .. '9' 
                                | '_' -> true
                        |   _ -> false

                in
                try (
                    while true do
                        if ( not (valid_char testString.[!count])  ) then
                            testString.[!count] <- '_';

                        count := !count + 1
                    done;
                    testString
                ) with
                | Invalid_argument(_) -> testString
            end
        in
        mod_string lower_name;
    end
 
(*  This method is specifically for creating a copy of the given expression.
 *  Nothing big deal.
 * *)
let rec copy_exp (givenExp : exp) : exp =
    match givenExp with
    (*  No more recursion in these cases because they do not contain any more
     *  expressions.
     * *)
    |   Const(_)
    |   Lval(_)
    |   SizeOf(_)
    |   SizeOfStr(_)
    |   AlignOf(_)
    |   AddrOf(_)
    |   StartOf(_) -> givenExp
    |   SizeOfE(currExp) ->
            let newExp = copy_exp(currExp)
            in
            SizeOfE(newExp)
    |   AlignOfE(currExp) ->
            let newExp = copy_exp(currExp)
            in 
            AlignOfE(newExp)
    |   UnOp(op1, currExp, type1) ->
            let newExp = copy_exp(currExp)
            in 
            UnOp(op1, newExp, type1)
    |   BinOp(op1, currExp1, currExp2, type1) ->
            let newExp1 = copy_exp(currExp1)
            and newExp2 = copy_exp(currExp2)
            in 
            BinOp(op1, newExp1, newExp2, type1)
    |   CastE(type1, currExp) ->
            let newExp = copy_exp(currExp)
            in 
            CastE(type1, newExp)

let rec copy_init (currInit : init) : init =
    match currInit with
    |   SingleInit(currExp) -> SingleInit((copy_exp currExp))
    |   CompoundInit(givenType, offset_init_list) ->
            CompoundInit(   givenType, 
                            (List.map copy_offset_init offset_init_list)
                        )

and copy_offset_init (givenOffset, givenInit) : (offset * init) =
    (givenOffset, (copy_init givenInit))

(*
 * Check if given function is to be skipped from
 * bounds processing.
 *
 * Since bounds introduction is a 3rd run, i.e., after instrumenting
 * pointer dereferencing, we need to skip processing of functions
 * which were not present originally in the file, but were introduced
 * by transformation and/or instrumenting pointer dereferencing.
 * 4 functions used in the function below are such example.
 *)
let skipFunction (name : string) (file_name : string) : bool =
  (*  Names of functions used in the file for initializing and
   *  de-initializing guardzones. There are 3 such functions. One for array
   *  definitions, array declarations and one for the rest of the
   *  variables.
   *  We need to skip processing these functions for bounds.
   *  
   *  See skipFunction implementation.
   *)
  let global_name_arr_defn =  file_name ^ suffix_array_defn
  and global_name_arr_decl =  file_name ^ suffix_array_decl
  and global_name_ptr_defn =  file_name ^ suffix_ptr_defn
  and global_name_default =  file_name ^ suffix_default
  in
     begin
            (   (name = global_name_arr_defn) ||
                (name = global_name_arr_decl) ||
                (name = global_name_ptr_defn) ||
                (name = global_name_default)  
            )
     end

(*===========================================================================*)
(*  In this section we will consolidate all the functions that involve retrieval
 *  of the fields of a guardzone struct, testing for a guardzone struct.
 * *)

(*  A simple utility function to get the compfield from a Struct-type variable    *)
 let getVarStruct (transVar:varinfo) : compinfo = 
        begin
            match transVar.vtype with
            | TComp(compInfo, _) -> compInfo
            | _ -> raise (Incorrect_Input ("[getVarStruct]Transformed Variable" ^
                                "not a structure"))
        end           

(*  A simple utility function to get a specified field from a variable that is
 *  known to be a structure.
 * *)
let getVarField (transVar : varinfo) 
                  (fieldName : string ) : fieldinfo =                      
    let transStruct  = getVarStruct transVar
    in
    (Cil.getCompField transStruct fieldName)

let getLvalStruct (field:fieldinfo) : compinfo = 
    begin
       match field.ftype with
        | TComp(compInfo, _) -> compInfo
        | _ -> raise (Incorrect_Input ("[getVarStruct]Transformed Variable" ^
                                       "not a structure"))
    end

(*  A simple utility function to get a specified field from a variable that is
 *  known to be a structure.
 * *)
let getLvalField (transLval : lval) 
                  (fieldName : string ) : fieldinfo =                      
    match transLval with
    (Var(vinfo),Field(fld,_)) ->
      let transStruct  = getLvalStruct fld
      in
      (Cil.getCompField transStruct fieldName)
    | _ -> raise (Incorrect_Input ("[getLvalField] Transformed variable" ^
                                    "not inside a structure"))

(*  This method confirms that the variable passed as a parameter is a
 *  transformed variable.
 *  *)
let is_gz_var (transVar : varinfo) : bool =
    try (
        ignore(getVarField transVar fld_front);
        true
    )
    with 
    |  _  -> false

(*
 * Get the size of a type in int
 *)
let sizeOfType (vtype : typ) : int = 
  let size = (Cil.constFold true (Cil.sizeOf vtype))
  in
  match size with
    |   Const(CInt64(value, _,_)) -> (Int64.to_int value)
    |   _ -> raise (Incorrect_Input ("Constant folding results" ^
                                    " does not result in value"))

(*  Note that incomplete transformation is mainly used in two cases:
    *  Incomplete structures.
    *  Variable sized stack arrays.
 * *)
let is_incomplete_transformation (transVar : varinfo) : bool =
    begin
        if (is_gz_var transVar) then
            try (
                (*ignore(getVarField transVar fld_rear); *)
                if(Hashtbl.mem isInCompleteTypeTbl transVar.vtype) then
                  true
                else
                  false
            )
            with 
            |  _  -> false
        else
            raise (Incorrect_Input "[is_incomplete_transformation] supplied variable NOT a
                transformed variable" )
    end

(*  The basic objective of this method is only to generate the offset*init list
 *  for each of the guardzones. Note that this is NOT dependent of which variables
 *  guardzones are being initialized. *)
let guardzone_init (size : int) : init = 
    
    let rec init (size : int) : (offset * init) list =
        let index_exp = Const( CInt64( (Int64.of_int (size - 1)), IUInt, None) )
        in

        let index = Index(index_exp, NoOffset)
        in
        if size <= 0 then
            []                
        else
            (index, SingleInit(zone_value_exp)) :: (init (size - 1))

    and size_exp = Const(CInt64((Int64.of_int size), IUInt, None))
    in

    let zone_type = TArray(TInt(IUInt, []), Some(size_exp), [])
    in
    
    CompoundInit(zone_type, (init size))

(*
 * Debugging print function for CCured analysis
 *)
let print_CCured_node_kind (n_node : Ptrnode.node) : unit =
  (*if(not !dontUseCCuredAnalysis) then
    let kind_str = if(n_node.Ptrnode.kind = Ptrnode.Safe) then
      "Safe"
    else
      "Unsafe"
    in
      (print_string ("\nNode id = " ^ (string_of_int n_node.Ptrnode.id) ^
                     " kind = " ^ kind_str))
  else
      () *) ()

(*
 * Function to check if the specified type is SAFE or UnSAFE as per
 * CCured's analysis
 *)
let isSafeType (attrs : attributes) : bool =
  if(not !dontUseCCuredAnalysis) then
    let n_node_opt : Ptrnode.node option = Ptrnode.nodeOfAttrlist attrs
    in
    let n_node = match n_node_opt with
                  Some n -> n
                  | None -> raise (Incorrect_Input "type doesn't have node
                  associated for it")
    in
    begin

      print_CCured_node_kind n_node;

      if(n_node.Ptrnode.kind = Ptrnode.Safe) then
        true
      else
        false
    end
  else
    false

let isSafeExp (expr : exp) : bool =
    let n_node_opt = Ptrnode.nodeOfType (typeOf expr) in
    let n_node = match n_node_opt with
                  Some n -> n
                  | None -> raise (Incorrect_Input "type doesn't have node
                  associated for it")
    in
    begin

      print_CCured_node_kind n_node;

      if(n_node.Ptrnode.kind = Ptrnode.Safe) then
        true
      else
        false
    end

(*
 * This functions initializes the hash table
 * used for replacing calls to memory management functions with their
 * original versions in case the pointer used/returned by
 * function is SAFE.
 *
 * Key - name of the function
 * value - pair of int list and string of which
 *         int list is the list of number of parameter for the function prototype
 *         which should be checked for safe/unsafe.
 *
 *         string is actual name of that function in the transformed
 *         glibc.
 *)
let initMemMgmtFuncsHT = 
    begin
    (* 
     * 0 indicates that the return pointer must be checked
     * for safe/unsafe.
     *)
    (Hashtbl.add memMgmtFuncsPtrParamTbl "malloc" ([0],"orig_malloc"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "calloc" ([0],"glibc_calloc"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "valloc" ([0],"orig_valloc"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "memalign" ([0],"orig_memalign"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "pvalloc" ([0],"orig_pvalloc"));

    (Hashtbl.add memMgmtFuncsPtrParamTbl "malloc2" ([0],"orig_malloc"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "calloc2" ([0],"glibc_calloc"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "valloc2" ([0],"orig_valloc"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "memalign2" ([0],"orig_memalign"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "pvalloc2" ([0],"orig_pvalloc"));

    (* 
     * 1 indicates that the 1st input argument pointer must be checked
     * for safe/unsafe.
     *)
    (Hashtbl.add memMgmtFuncsPtrParamTbl "realloc" ([0;1],"orig_realloc"));
    (Hashtbl.add memMgmtFuncsPtrParamTbl "free" ([1],"orig_free"));

    (Hashtbl.add memMgmtFuncsPtrParamTbl "realloc2" ([0;1],"orig_realloc"));
    end

(*
 * A hash table that contains mapping between memory allocation
 * functions and their wrapper names.
 *)
let initMemMgmtFuncsWrappersHT =
    begin
    (Hashtbl.add memMgmtFuncsWrappersTbl "malloc"   "malloc2");
    (Hashtbl.add memMgmtFuncsWrappersTbl "calloc"   "calloc2");
    (Hashtbl.add memMgmtFuncsWrappersTbl "realloc"  "realloc2");
    (Hashtbl.add memMgmtFuncsWrappersTbl "valloc"   "valloc2");
    (Hashtbl.add memMgmtFuncsWrappersTbl "pvalloc"  "pvalloc2");
    (Hashtbl.add memMgmtFuncsWrappersTbl "memalign" "memalign2");
    end

(*
 * This hash table contains the names of untransformed memory allocation
 * functions. This is used for fast lookup.
 *)
let initUntransformedMemAllocFuncNamesHT = 
    begin
      (Hashtbl.add untransformedMemAllocFuncNamesTbl "orig_malloc" 1);
      (Hashtbl.add untransformedMemAllocFuncNamesTbl "glibc_calloc" 1);
      (Hashtbl.add untransformedMemAllocFuncNamesTbl "orig_valloc" 1);
      (Hashtbl.add untransformedMemAllocFuncNamesTbl "orig_memalign" 1);
      (Hashtbl.add untransformedMemAllocFuncNamesTbl "orig_pvalloc" 1);
    end

(*  The following two functions classify types into two different
 *  categories : fixed_type and incomplete_type
 *  *)
(*  This is a pretty simple method to check if the type is an fixed type.
 *  For the purposes of this instrumentation, fixed type is something whose size can be
 *  determined by CIL. So it definitely does includes built in types and does
 *  not include structures and unions, hence the name.
 *  We have this because at a global level we may have ONLY the declaration of
 *  an aggregate type and not the definition and hence instrumentation cannot be
 *  done based on the size of the structure or union.
 * *)
let is_fixed_type (givenType : typ) : bool =
    let currType = (Cil.unrollTypeDeep givenType ) in
    let sigString = Pretty.sprint 80 (d_typsig () (Cil.typeSig currType))
    in
    match currType with
    |   TVoid (_) | TFun(_,_,_,_) | TNamed(_,_) | TBuiltin_va_list(_) ->
            raise (Incorrect_Input ("[is_fixed_type] Size not defined for "
                      ^ sigString))

    |   TInt(_, _) | TFloat (_,_) | TPtr(_,_) | TEnum(_,_) -> true

    |   TArray(_, _, _) | TComp(_, _) -> false


 (*  The basic objective of this function is to check if the
  *  specified type is a structure and that too an incomplete
  *  one.
  *  The second argument specifies whether we are checking the
  *  type of field of the original structure. This is needed
  *  because any type can be supplied to this function. In such a
  *  case , an array type with no specified length is fine.
  *  However if the last field of a structure is an array without
  *  a length parameter, that is a problem.
  *  Hence the second argument helps distinguish the two cases.
  *
  *  Note that we must have the complete structure definition for this function
  *  including the definitions of all the fields. Else we just throw an
  *  exception.
  * *)
let rec is_incomplete_struct (givenType : typ) (isField : bool) : bool =
                    
    let structType = (Cil.unrollTypeDeep givenType)
    in

    (*  The basic objective of this function is to return the
     *  last element of the givenList.
     *  The basic idea is to keep traversing the list till no
     *  more elements are left in the tail.
     *  Return Failure "hd" if the list is empty.
     *  *)
    let rec traverse_list (givenList : 'a list) : 'a =
        let head = List.hd givenList
        in
        
        try (
            let tail = List.tl givenList
            in
            (traverse_list tail)
        )
        with
        |   Failure (_) -> head
    in

    match structType with

    (*  Thus we have an incomplete type ONLY when the array at
     *  the end does not have a size or size == 0.
     * *)
    |   TArray(_, None, _) when isField -> true 

    (*  Note that for any structure whose definition we do not
     *  have, we cannot decide anything. 
     *  This could have been handled Cil.isCompleteType. So we
     *  throw an exception 
     * *)
    |   TComp (currCompInfo, _ )  when 
                ( currCompInfo.cstruct && (not
                (Cil.isCompleteType structType ))) ->
                
                    true

    (*  This case deals with the case that the structure
     *  definition is available
     * *)
    |   TComp (currCompInfo, _ )  when currCompInfo.cstruct ->
            begin
                try (
                    let final_field =
                        (traverse_list currCompInfo.cfields)
                    in
                    (is_incomplete_struct final_field.ftype true)
                )
                with

                (*  This case basically implies that the list is
                 *  empty and has no head. Thus it's just a
                 *  declaration and hence we cannot do anything
                 *  about it
                 * *)
                |   Failure (_) ->
                        raise (Incorrect_Input (
                            "[is_incomplete_struct]" ^
                            " We do not have structure definition." ^
                            " Nothing can be done about this." )
                            )
            end

    |   _ -> false


(*  Here the objective is to find if the given type is a struct declaration. 
 *  Hence we check to see if the supplied type is a struct that has not been
 *  defined. CIL directly supplies us a field in compInfo to do so.
 * *)
let is_type_defined (givenType : typ ) : bool =
    let varType = (Cil.unrollTypeDeep givenType)
    in

    match varType with
    |   TComp(currCompInfo, _) -> currCompInfo.cdefined
    |   _ -> true

(*===========================================================================*)

(*  The basic idea of this function is to recursively go through all offsets to
 *  check if there has been an array access. If there has been, then the lval to
 *  which this offset belongs, would need to be either bounds-checked or guardzone
 *  checked *)
let rec has_array_access (currOffset : offset) : bool =
    match currOffset with
    |   NoOffset -> false
    |   Index(_, _) ->true
    |   Field(_, newOffset) -> (has_array_access newOffset)

(*  This value has been defined at the "global" level because both the
 *  instrVisitor and transVisitor must use the same value for deciding whether
 *  an array should be guardzoned or not. *)
(*  This value is used for deciding whether variable of a given type should
 *  have index checking applied to it as opposed to guardzone check.
 *  The function checks whether the lval access is an array index access with
 *  two conditions
 *      1.  The Index access occurs at the top-level
 *      2.  There are no further index offsets further after top-level index
 *          access. That would indicate either a multi-dimensional array or an
 *          array within a struct or both
 *
 *  Note that the function works for untransformed variables as well as
 *  untransformed variables.
 *  *)
let has_simple_array_acc (currLval : lval) : bool = 
    match currLval with

    (*  The case below matches the two conditions specified above in case of
     *  untransformed variables   *)
    |   (Var(currVar), Index(_, newOffset)) ->
            (not (has_array_access newOffset))

    (*  The case below matches the two conditions specified above in case of
     *  transformed variables   *)
    |   (Var(currVar), Field(currField, newOffset)) ->
            begin

                (*  The basic idea here is that to see if we are meddling with
                 *  orig_field of a transformed variable  ...  *)
                if ((is_gz_var currVar) && (currField.fname = var_field_name))
                then
                    match newOffset with

                    (*  If we are, then we check to see if we are looking at a
                     *  single dimensional array without any other index offsets    
                     *  *)
                    |   Index(_, remOffset) -> (not (has_array_access remOffset))
                    |   _ -> false
                else
                    false

            end

    (*  All the rest of cases indicate a variable access of the following cases:
     *      1.  Pointer dereference
     *      2.  Multi-dimensional array
     *      3.  Array within a struct
     *      4.  Combination of all.
     *  *)
    |   _ -> false

(*  The objective of the method below is to check whether the given variable is
 *  a transformed variable, an incomplete transformation AND an array
 *  declaration.
 *  *)
let is_array_decl (transVar : varinfo) : bool =
    begin
        if (is_incomplete_transformation transVar) then
            let orig_var = getVarField transVar var_field_name
            in
            match orig_var.ftype with
            |   TArray(_, None, _ ) -> true
            |   _ -> false

        else
            false
          
    end

(*===========================================================================*)

(*  The objective of this method is to check whether the given global element
 *  should be undergo variable transformation. This DOES NOT apply to
 *  function global objects.
 *  Every function global object will need to be processed for change in
 *  variable access corresponding to transformed variables.
 * *)
let permitTransformation (currGlob : global) : bool =
    begin
        start_method ();
        log (text "permitTransformation : ");
        log (text ("currGlob.location.file: " ^ (get_globalLoc currGlob).file));
        log unalign;

        (*  Note that in this function we will iterate over all files 
         *  in the system directories list to see if any one of them is the
         *  prefix of file name given to us.
         *  For this purpose of "matching" we will use the match_file_name 
         *  function
         *)  
        let is_sys_file (file_name : string) : bool =
            (*  Note that here file_name is location of the global 
             *  element while dir_name is name of the directory in the 
             *  list that we have been supplied at the start of the 
             *  transformation *)
            let match_file_name (file_name : string ) 
                                (dir_name : string ) : bool =

                (*  Note that this regular expression is basically to
                 *  check if the dir_name is the prefix of supplied file
                 *  name    *)
                let prefix_regexp = Str.regexp 
                                    ((Str.quote dir_name) ^ ".*")
                in
                (Str.string_match prefix_regexp file_name 0)
            in

            try (
                ignore (List.find (match_file_name file_name) !sys_dirs_list);
                true
            ) with 
            |   Not_found ->    false
    
        and currGlobFile = (get_globalLoc currGlob).file
        and symbol_present (string_list: string list) (chk_name : string) : bool =
                begin
                    log(text ("is this symbol present: " ^ chk_name));
                    try (
                        ignore (List.find 
                            (fun (symbol_name : string) -> chk_name = symbol_name)
                            string_list
                        );
                        true
                    )
                    with 
                    |   Not_found -> false
                end

        in

        (*  Check if the current element is present in the global list of
         *  symbols that are not to be transformed
         *  *)
        let is_restricted_symbol = (symbol_present !symbols_list)
        in

        match currGlob with
        (*  A small method to check when the current global element has been specified
         *  in the symbols file. If it has been, then it should not be transformed 
         *  Moreover, when a symbol belongs to a system header file, then it should
         *  not be transformed as well.
         *)
        |   GVar(currVarInfo, _, _ )
        |   GVarDecl(currVarInfo, _) when ((is_sys_file currGlobFile) ||
                    is_restricted_symbol(currVarInfo.vname)) ->
                        begin
                            log(text ("Permission denied for symbol: " ^
                            currVarInfo.vname));
                            false
                        end

        | _ -> true
    end

(*  The objective of this method is to check whether the given global element
 *  function should be instrumented. This applies ONLY for function global 
 *  objects.
 *  Note that the further line ranges checking will needed to be done later
 *  again.
 * *)
let permitInstrumentation (currGlob : global) : bool =
    begin
        start_method ();
        log (text "permitInstrumentation : ");
        log (text ("currGlob.location.file: " ^ (get_globalLoc currGlob).file));
        log unalign;

        (*  Note that in this function we will iterate over all files 
         *  in the system directories list to see if any one of them is the
         *  prefix of file name given to us.
         *  For this purpose of "matching" we will use the match_file_name 
         *  function
         *)  
        let is_sys_file (file_name : string) : bool =
            (*  Note that here file_name is location of the global 
             *  element while dir_name is name of the directory in the 
             *  list that we have been supplied at the start of the 
             *  transformation *)
            let match_file_name (file_name : string ) 
                                (dir_name : string ) : bool =

                (*  Note that this regular expression is basically to
                 *  check if the dir_name is the prefix of supplied file
                 *  name    *)
                let prefix_regexp = Str.regexp 
                                    ((Str.quote dir_name) ^ ".*")
                in
                (Str.string_match prefix_regexp file_name 0)
            in

            try (
                ignore (List.find (match_file_name file_name) !sys_dirs_list);
                true
            ) with 
            |   Not_found ->    false
    
        and currGlobFile = (get_globalLoc currGlob).file
        in

        (*  Check if the current function is present in the list of function
         *  that are to be exclusively transformed. Note that this functionality
         *  is to be activated ONLY if the list is non-empty.
         * *)
        let is_permitted_function (name : string) : bool =
            (*  If functions_list is empty then we must do as follows:
             *    exclusive instrumenting     -   return false
             *    exclusive non-instrumenting -   return true
             * *)
            if ((Hashtbl.length functions_list) = 0) then
                (not !doInstrument)
            else
                try (
                    (*  If doInstrument is set to true, then try to find the
                     *  functions name.
                     * *)
                    if (!doInstrument) then
                        begin
                            let _ = (Hashtbl.find functions_list name) in
                            true
                        end
                    else 
                        begin
                            (*  Note that in case of exclusive
                             *  non-instrumentation, we will have to check if
                             *  along with functions name, line ranges. If they
                             *  are, then the function must be permitted to be
                             *  instrumented and further decision must be made
                             *  at element level.
                             * *)
                            let line_ranges = (Hashtbl.find functions_list name)
                            in

                            (*  If no line_ranges are present, then do not
                             *  instrument the functions
                             * *)
                            if ((List.length line_ranges) = 0) then
                                false
                            else
                                true
                        end
                ) with
                | Not_found -> 
                        if !doInstrument then
                            (*  If exclusive instrumenting is on and the function
                             *  was NOT found, then return false
                             * *)
                            false
                        else
                            (*  If exclusive non-instrumenting is on and the function
                             *  was NOT found, then the function must be
                             *  instrumented.
                             * *)
                            true
        in

        match currGlob with
        (*  For deciding whether functions are to be instrumented or not, we
         *  use the list of directories that include system header files.
         *  *)
        |   GFun(currFun, _ ) when (is_sys_file currGlobFile)->
                    begin
                        log(text ("Permission denied for symbol: " ^
                        currFun.svar.vname));
                        false
                    end

        (*  Now if the function is NOT a system header file function, and IF it's
         *  NOT allowed to be transformed, then return false.
         *  A function is NOT allowed to be instrumented, when the
         *  functions_list is NOT empty and current functions name is NOT
         *  present in the list
         * *)
        |   GFun(currFun, _ ) when (not (is_permitted_function
                                        currFun.svar.vname)) ->
                    begin
                        log(text ("Permission denied for symbol: " ^
                        currFun.svar.vname));
                        false
                    end

        |   GFun(currFun, _ ) -> 
                begin
                    log(text ("Permission granted for symbol: " ^
                        currFun.svar.vname));
                    true
                end

        | GVarDecl(_,_) when (is_sys_file currGlobFile) -> false
        |   _ -> true

    end

(*===========================================================================*)

(*  The objective of this class is to simply scan a given expression to see if
 *  contains any reference to an extern variable whose type is only declared and
 *  not defined
 * *)
class expressionScanner (varReplacementTable : (varinfo, varinfo)Hashtbl.t)
                    (f:file) =
    object (self)
        inherit nopCilVisitor
        (*=====================================================================*)
        (*  The first section comprises of all the state variables of this
         *  object
         *  *)
        val mutable init_exceptional_case = false
        method is_exceptional_case = init_exceptional_case

        (*=====================================================================*)

            (*  We have to over-ride this method this method because there is
             *  one very specific expression that we would like to replace.
             *  If the expression is of the form &(global_var_decl) where
             *  global_var_decl has type which is only declared and not defined,
             *  we cannot replace it by &( *global_var_ptr).
             *  Hence this kind of expression MUST be replaced with directly
             *  global_var_ptr.
             * *)
            method vexpr (currExpr : exp ) : exp visitAction =
                match currExpr with
                |   AddrOf(currLval)  ->
                        begin
                        match currLval with
                        |   (Var(oldVar), NoOffset)when Hashtbl.mem varReplacementTable oldVar ->                   
                                begin
                                    let transVar = Hashtbl.find varReplacementTable oldVar
                                    in

                                    (*  Note that the transformedVariable type can be EITHER
                                     *  a pointer or a transformed structure.
                                     *  The Pointer case happens STRICTLY ONLY FOR global
                                     *  variables when their types are ONLY declared and NOT
                                     *  defined. In such case, we are forced to use the
                                     *  pointer.
                                    * *)
                                    let transVarType = (Cil.unrollTypeDeep transVar.vtype)
                                    in

                                    match transVarType with
                        
                                    (*  This case happens STRICTLY ONLY FOR global
                                     *  variables when their types are ONLY declared and NOT
                                     *  defined. In such case, we are forced to use the
                                     *  pointer dereference.
                                     *
                                     *  In such a case, we change the current
                                     *  node from &(global_var_decl) to
                                     *  trans_global_var_ptr
                                     *)

                                    |   TPtr(_,_ ) -> 
                                            begin
                                                init_exceptional_case <- true;
                                                ChangeTo(Lval(Cil.var transVar))
                                            end

                                        (*  Else proceed as you always would.
                                        * *)
                                    |   _ -> DoChildren

                            end

                        |   _ -> DoChildren
                        end

                |   _ -> DoChildren

    end
 
(*===========================================================================*)

(*  The objective of an object of this class is to instrument all the pointer
 *  dereferences. 
 *  This class constitutes the second "sweep"/"run" of the target file after both
 *  the global variables and the local variables have been transformed. *)    
class instrVisitor  (f:file) =
    object (self)
        inherit nopCilVisitor

        val is_char_guard = emptyFunction "is_char_guard"
        val is_data_guard = emptyFunction "is_data_guard"                    
        val is_guard      = emptyFunction "is_guard"
        val is_array_acc_unsafe = emptyFunction "is_array_acc_unsafe"

        (*  Note that we will be including conditional "abort" statements in the
         *  original code. The abort will be triggered if the guardzone check
         *  statements.
         *  Note that gz_abort is actually a macro defined in zcheck.h
         * *)
        val gz_abort = emptyFunction "gz_abort"

        (*  Note that the variable below is just a dummy variable and is never
         *  actually used.
         *  Instead every function will have such a local variable that will be
         *  used.
         *  The variable below is thus used to "point" to the current functions
         *  abort variable.
         *  This will be used in the method processPtr to store the value
         *  returned by the guardzone check functions.
         * *)
        val mutable curr_abort_var  = dummy_global_var

        (*  This value contains the line ranges for the current function. Note
         *  that if functions_list is empty OR if functions_list does not
         *  contain the current function, then the value of this variable will
         *  be an empty list.
         *)
        val mutable curr_line_ranges = None

        (*  This value is set on a per statement basis whether the expressions
         *  in the current statement must be instrumented or not. This is needed
         *  because a statement can contain children statement and while it
         *  itself must not be instrumented, its children may need to be, thus
         *  creating a catch22 situation.
         * *)
        val mutable do_instrument = false

        (*  The basic idea of this flag is that it must be set whenever we come
         *  across an addressOf expression. In that case, the child expression
         *  is not guardzone checked even if it "looks" like a memory dereference
         *  because it is ACTUALLY an address computation.
         *  For eg &(ptr->field) is NOT a memory dereference but actually an
         *  address computation.
         * *)
        val mutable addressOfFlag = false

        (*  The basic idea of this variable is to hold all the pointer
         *  dereference expressions for a statement. Only when the visitor
         *  object exits the statement node, then all the guardzone checks for the
         *  expressions are added to the program.
         *  This variable is a stack because statements can be nested and we
         *  need to keep track of the expression list for each statement.
         *)
        val mutable stmtExprStack = Stack.create ()

         (*  While adding expressions to these lists, we make sure that the
         *  expression does not exist in the list already. This is the crucial
         *  part. We thus ensure that an expression is checked only once.
         * *)
        (*  Note that thus either a statement or an instruction can
         *  have its expressions examined at a time, which is what makes sense. 
         *  If we get a statement within another statement, it's the 
         *  responsibility of the second to put the first in the stmtExprStack.
         * *)
        val mutable currExprList : exprSourcePair option = None

        (*  The objective of this variable is to maintain information whether a
         *  cast has been performed on the given lval. For eg: 
         *   (unsigned int) ptr->field.
         *   Note that in this case, we must ensure that is_char_guard recognizes
         *   that the type is unsigned int and nothing else.
         * *)
        val mutable currCastType : Cil.typ option = None

        (*  The basic objective of this flag is to check when the lval being
         *  considered is the right hand side of set instruction. In such a case, if the
         *  instrReadsOnly flag is set, then the lval is NOT instrumented. Else it
         *  is.
         * *)
        val mutable setLval = false

        (*  Value used for logging  *)
        val class_name = text "instrVisitor"

        (*===================================================================*)

             (*  This function checks if the current element (stmt/instr) is to be
             *  instrumented or not.
             *  There are two cases when the current statement
             *  will be allowed to be instrumented.
             *  1.  doInstrument is FALSE and the functions_list is empty, 
             *      then all the elements are to be instrumented.
             *  2.  doInstrument is TRUE and the functions_list is empty: This
             *      case will be caught at the function level. Hence it won't
             *      arise here.
             *  2.  The functions_list is NOT empty and the current function is
             *      one of the specific functions. Then we must check the
             *      line number against all the line number ranges.
             *
             * *)
        method private permit_element (line_number : int) : bool =
            (*  CASE 1:
             *  If in exclusive non-instrumenting mode and the
             *  Functions_list is empty and All elements must be instrumented. 
             * *)
            if ((not !doInstrument ) && ((Hashtbl.length functions_list) = 0)) then
                true

            else
                begin
                    (*  Retrieve the list of line ranges and check if the
                     *  current stmt belongs to any of them.
                     * *)
                    let check_range (curr_line_no : int) 
                                    ((range_start,range_end) : (int*int)) : bool
                                    =
                        begin

                            log (text ("[check_range] curr_line_no : " 
                                            ^ (string_of_int curr_line_no)));                                            
                            log (text ("[check_range] range_start, range_end : " 
                                            ^ (string_of_int range_start) ^ " , "
                                            ^ (string_of_int range_end)));                                            
                            if ((curr_line_no >= range_start) && (curr_line_no <= range_end)) then
                                begin
                                    log (text ("[check_range] statement " ^
                                    (string_of_int curr_line_no)^ " permitted"));                                    
                                    true
                                end
                            else
                                false
                        end
                    in

                    let check_curr_range = (check_range line_number)
                    in

                    match curr_line_ranges with
                    (*  CASE 2:
                     *  If in exclusive non-instrumenting mode and the functions
                     *  name did not turn up in the functions_list, then all
                     *  elements must be instrumented.
                     *
                     *  The curr_line_ranges matching None with exclusive
                     *  instrumenting mode CANNOT happen. Because if a functions
                     *  name is present in the list, but no line ranges are
                     *  specified, then the line_ranges is an
                     *  empty list
                    * *)    
                    | None ->   if (not !doInstrument) then
                                    true
                                else
                                    raise (Incorrect_Input "[permit_element] Empty Line ranges list NOT expected")
                    
                    (*  Note that we pick up the valid line ranges from the
                     *  object state variable.
                     * *)
                    | Some(line_ranges) -> 
                            (*  Note that a null list in functions_list implies
                             *  that the entire function must be instrumented.
                             *  This is because if line_ranges is empty and we
                             *  are in exclusive NON-instrumenting mode, then we
                             *  would have detected this in
                             *  permitInstrumentation function itself
                             * *)
                            if (line_ranges = []) then
                                true
                            else                                

                                let range_check_positive = 
                                    (List.exists check_curr_range line_ranges)
                                in

                                (*  CASE 3 and CASE 4:
                                 *)
                                (*  IF in exclusive NON-instrumenting mode, then
                                 *  current element must NOT be in range, else
                                 *  if exclusive INSTRUMENTING MODE then it MUST
                                 *  exist within range.
                                 * *)
                                if (!doInstrument) then
                                    range_check_positive
                                else
                                    (not range_check_positive)
                end

        (*  The basic objective of this method is to get the Ptr component of
         *  an pointer expression if it exists, else throw a Not_a_Pointer
         *  exception.
         *  An important condition is that we examine expressions with only one
         *  "level" of pointer dereference :
         *  I.e., *( p + 5) - valid
         *       *( *p + 5) - not considered. 
         *  This is because, we want to "optimize" only simple array and pointer
         *  expressions
         *  *)
        (*  Note that there are few assumptions that I have made:
            *  1.   Unary operation CANNOT give a pointer type  
            *  2.   We will explore the CastE option to make sure that
            *       expression is not just a pointer of different type
            *       E.g., ((int * ) char_ptr) - [Correction: This option is no
            *       longer considered. See the pattern for explanation.] 
            *)

        method private getPtrFromExpr (currExpr : exp) : lval =
            begin
                start_method ();
                log (class_name ++ text ".getPtrFromExpr : ");
                log (text "currFunc:fundec : " ++ (dn_exp () currExpr));
                log unalign;

            let exprType = Cil.typeOf currExpr
            and isPointerOp (op : binop) : bool =
                begin
                    match op with
                    |   PlusPI |   IndexPI |   MinusPI -> true
                    |   _   -> false
                end

            (*  The basic objective of this method is to get the Array component of
             *  from a given lval if it exists else thrown Not_a_Pointer expression *)
            and getPtrFromLval (currLval : lval) : lval =
                    begin
                        match currLval with
                        (*  Note that the reason why we are not concerned
                         *  about any offset here is because whatever it is,
                         *  it is contributing to making this a pointer
                         *  access.   *)
                        |   (Var(_), _ ) -> currLval

                        (*  Note that the whole point of this exercise is
                         *  NOT to go deeper and deeper into the hierarchy,
                         *  but the pointer variable used. Hence
                         *  E.g., in *(p + 5), answer is p
                         *  However in * ( *p + 5), we raise an exception *)
                        |   _ -> raise Not_a_Pointer
                    end

            in
            begin
                match exprType with
                (*  The given expression is of pointer type. 
                 *  Proceed as planned. *)
                |   TPtr(_,_)  ->
                        begin
                            match currExpr with
                            |   Lval(currLval) -> getPtrFromLval currLval

                            (*  Note that only one of the expressions must have
                             *  pointer type. Hence we will "explore" the one
                             *  that has pointer type   *)
                            |   BinOp(binOp, exp1, exp2, expType) when
                                                (isPointerOp binOp) -> 
                                    begin
                                        let exp1Type = Cil.typeOf exp1
                                        in
                                        if (Cil.isPointerType exp1Type) then
                                            self#getPtrFromExpr exp1
                                        else
                                            self#getPtrFromExpr exp2
                                    end
                            (*  Note that in case of & operation, we are
                             *  interested in exactly the opposite type of lval.
                             *  We are not interested in Var() but rather Mem().
                             *  Because & of Mem cancel each other. *)
                            |   AddrOf(currLval) ->
                                    begin
                                        match currLval with

                                        (*  This pattern caters to the
                                         *  expression &(array[10]) 
                                         *  This is another case where & and
                                         *  subscript variable "cancel" each
                                         *  other.  *)
                                        (*  Note that what we return is only the
                                         *  array variable and not its index *)
                                        |   (Var(currVar), Index(_, NoOffset))  ->
                                               (Var(currVar), NoOffset)
                                        

                                        (*  Other types of offsets are again not
                                         *  considered because they were not
                                         *  pointers by default and were
                                         *  "converted" into pointers by addrOf
                                         *  operation   *)
                                        |   (Mem(expr), NoOffset) ->
                                                self#getPtrFromExpr expr
                                        
                                        (*  Note that here we raise an exception
                                         *  because the lval used is not a
                                         *  pointer by default but had the &
                                         *  operation applied to it *)
                                        |   _   -> raise Not_a_Pointer
                                    end

                            
                            (*  Here we are assuming that the lVal being given
                             *  to us is of array type  *)
                            |   StartOf(currLval) -> currLval

                            (*  Note that we will NOW not consider the CastE
                             *  case because if an array is being cast to
                             *  another type, even an array, then we have no way
                             *  to calculate the new array-length   *)
                            (*|   CastE (_, castExp) -> getPtrFromExpr castExp *)
                            |   _   -> raise Not_a_Pointer
                        end
                |   _ -> raise Not_a_Pointer
            end
            
            end

        (*  The basic objective of this method is to use the methods above to
         *  extract the pointer in the expression and check the pointer to see
         *  if it is an array variable that can be checked using index rather
         *  than guardzone checking   *)
        (*  Again. Do remember the arrays that can be index checked. Only single
         *  dimensional arrays with specified length can be checked. 
         *  And also if ptr points to any member within array, say ptr is
         *  because of some member of struct that is element of an array, then
         *  we are not interested in it *)
        method private isPtrArrayVar (expr : exp) : bool =
            (*  The basic utility of this method is to check that if the type of
             *  a given lval is an array, then if it has no offset, it implies
             *  that we are looking at a single dimensional array
             *  *)
            let has_no_offset (currLval : lval) : bool =
                match currLval with
                |   ( _, NoOffset)  -> true
                |   _   -> false
            in

            begin
                try (
                    let currPtr = self#getPtrFromExpr expr
                    in
                    let ptrType = Cil.typeOfLval currPtr
                    in
                    ( (Cil.isArrayType ptrType) && (has_no_offset currPtr)) 
                )
                with
                |   Not_a_Pointer -> false
            end

        (*  This method is to get the array variable being used in a given
         *  expression. If none such variable is present, then it throws a
         *  Not_an_Array exception *)
        method private getArrayFromExpr (expr : exp) : lval =
            (*  The basic utility of this method is to check that if the type of
             *  a given lval is an array, then if it has no offset, it implies
             *  that we are looking at a single dimensional array
             *  *)
            let has_no_offset (currLval : lval) : bool =
                match currLval with
                |   ( _, NoOffset)  -> true
                |   _   -> false
            in

            begin
                let currPtr = self#getPtrFromExpr expr
                in 

                let ptrType = Cil.typeOfLval currPtr
                in

                if ( (Cil.isArrayType ptrType) && (has_no_offset currPtr)) then
                    currPtr
                else
                    begin
                        log (text "getArrayFromExpr : Not an array exception
                        thrown for " ++ (dn_exp () expr));
                        raise Not_an_Array
                    end
            end

        (*===================================================================*)
        (*  The basic objective of this section is to define methods that
         *  actually introduce the calls to check the arrays and pointers. Why
         *  these are needed as separate methods is because in C an array
         *  reference can be disguised as Pointer dereference and vice versa.
         *  Hence the need to make such methods independent *)

        (*  This method basically takes in an array variable and an index, and
         *  depending on its type, generates the proper array index bounds
         *  check.
         *
         *  Note that the assumption made is that only single dimensional arrays
         *  are given to this method. IT DOES NOT check what kind of an array
         *  access has been supplied to it.
         *
         *  Moreover the arrayLval given to it, is actually an lval containing
         *  only the variable without any offset.
         *)
        method private processArrayVar (arrayLval : lval) (index : exp) : unit =
            let  processArray (index : exp) (array_size : exp) : unit = 
                let abort_var = ( Cil.var curr_abort_var) 
                
                in
                let call_array_acc = 
                        Call(Some(abort_var), Lval((Cil.var is_array_acc_unsafe.svar)),
                                    [index; array_size], locUnknown)

                and call_abort= Call(None, Lval((Cil.var gz_abort.svar)),
                          [(Lval(abort_var))], locUnknown)            

                in 
                begin
                    self#queueInstr [call_array_acc];
                    self#queueInstr [call_abort]
                end

            and arrayType = Cil.typeOfLval arrayLval
            in

            begin
                match arrayType with
                |   TArray(_, Some(arraySize), _) -> 
                        (processArray index arraySize);

                (*  If do not have the array size with us, then we must process
                 *  this as a pointer. 
                 *  This cannot be done here because we do not have the complete
                 *  lval with us. Thus pointer check queuing  must be done at the 
                 *  place where the call to this method was made.
                 *  *)
                |   TArray(_, None, _) ->
                        begin
                            log (text "processArrayVar : Not an array exception
                            thrown for " ++ (dn_lval () arrayLval));
                            raise Not_an_Array
                        end

                |  _ -> (*raise (Incorrect_Input "[instrVisitor.processArrayVar]
                Array object of different structure than expected")*) ();

            end


        (*  Note that here we are ASSUMING that the expression has ptr/array
         *  type. The decision we are trying to make is whether we should
         *  use the function for char guardzone detection (single check) or
         *  otherwise.
         *  HENCE, if the expr is NOT even a pointer, then the right thing
         *  to do is PROBABLY to just ignore this case.    *)

        method private processPtr   (addrPtr : exp) (derefValue : exp) 
                                    (origValue :exp): unit = 
            begin
                start_method ();
                log (class_name ++ text ".processPtr : ");
                log (text "addrPtr:expr = " ++ (dn_exp () addrPtr));
                log unalign;

            (*  While we are not using abort_var in is_char_guard, we will just
             *  keep this declaration till the implementation becomes more
             *  refined.
             * *)
            let abort_var = ( Cil.var curr_abort_var) 
            and char_guard_macro =  emptyFunction "is_char_guard"
            in

            let call_char_version = Call(None, Lval(var  char_guard_macro.svar), 
                [origValue; derefValue; addrPtr], locUnknown)                        

            and call_data_version = Call(Some(abort_var), Lval((var is_data_guard.svar)),
                          [addrPtr; SizeOfE(derefValue )], locUnknown)            
            
            and call_extended_version = Call(Some(abort_var), Lval((var is_guard.svar)),
                          [addrPtr; SizeOfE(derefValue)], locUnknown)            

            (*  Note that here we are calculating type such that all attributes
             *  such as const etc[Don't know which other ones exist] are
             *  ignored. *)
            and calcTypeSig = (Cil.typeSigWithAttrs (fun x -> []))

            in
            let isCharPtr (currPtr : exp) : bool = 
                let valueType = Cil.typeOf currPtr
                in
                (equals (calcTypeSig valueType) (calcTypeSig Cil.charPtrType))

            (*  Small helper utility to check if the given pointer type points
             *  to a structure  *)
            and isCompTypePtr (currPtr : exp) : bool =
                begin
                    let valueType = unrollTypeDeep (Cil.typeOf currPtr )
                    in
                    match valueType with
                    |   TComp(_ , _) -> true;
                    |   _   -> false;
                end
            in
            begin
                (*  Since char_guard_macro represents the is_char_guard macro, the
                 *  types of argument have to be reset for each macro
                 *  invocation.
                 * *)
                char_guard_macro.svar.vtype <- TFun(voidType, Some(
                    [ ("origValue", (Cil.typeOf origValue), []);
                      ("newValue", (Cil.typeOf derefValue), []);
                      ("ptr", (Cil.typeOf addrPtr), []);]), 
                       false, []);

                ignore (
                try( 
                    (*  We opted for extended checks. Hence perform more checks *)
                    if (!extendedCheck) then
                        if (isCharPtr addrPtr) then
                            self#queueInstr [call_char_version]
                        else
                            (*  If the pointer type that we have points to a
                             *  structure, use extended checks. Else use
                             *  first/last check as we know that the guardzone is
                             *  as large as any primitive data type *)
                            if (isCompTypePtr addrPtr) then
                                self#queueInstr [call_extended_version]
                            else
                                self#queueInstr [call_data_version]
                    else
                        (*  We have opted fast checks. Hence call the char
                         *  version for all the pointer dereferences.   *)
                        self#queueInstr [call_char_version]
                ) with 
                (*  Note that such an error is currently ignored. We
                 *  will need a more coherent strategy to deal with *)
                |   Not_a_Pointer   -> () ;

                );
            end

            end
 
        (*===================================================================*)
        (*  The basic objective of this section is to contain methods that help in
         *  the processing of to-be-guardzoned expressions contained in the
         *  variable currExprList.
         * *)        

        (*  The basic objective of this method is to do the preprocessing
         *  related to the bounds check lists setup when entering a statement
         * *)
        method private enterStmt (currStmt : Cil.stmt) : unit =
            begin
                ignore (
                match currExprList with
                |   None -> ()
                |   Some(currResourcePair) ->
                        begin
                            (*  Note that when we are inside a statement we do
                             *  not expect to have the currExprList allocated to
                             *  instruction. It MUST belong to another
                             *  statement.
                             * *)
                            ignore (
                            match currResourcePair.source with
                            |   CurrStmt(_) -> ()
                            |   CurrInstr(_ ) -> raise (Incorrect_Input
                                            "[enterSmt] We expected a statement
                                            here.")

                            );
                            (Stack.push currResourcePair
                                            stmtExprStack)   
                            ;
                        end

                );
                
                currExprList <- Some({   source = (CurrStmt(currStmt));
                                    exprList = []}
                                    )
            end

        (*  The basic objective of this method is to do the preprocessing
         *  related to the bounds check lists setup when entering an
         *  instruction.
         * *)
        method private enterInstr (currInstr : Cil.instr) : unit =
            begin
                ignore (
                match currExprList with
                |   None -> ()
                |   Some(currResourcePair) -> (Stack.push currResourcePair
                                                    stmtExprStack)
                );
                currExprList <- Some ({ source = CurrInstr(currInstr);
                                        exprList = [] }
                                     )
            end

        (*  This method basically queues one single expression, we run it
         *  over a list using the list methods.
         *  Note that it returns back a boolean value that indicates whether the
         *  next check must be skipped or not
         *  It also accepts a boolean value that specifies the current check
         *  must be skipped or not.
         *  This is because the expressionList will contain a guardzone check for
         *  every array reference. If the array-bounds check is successful
         *  then we will not do the guardzone check. Hence we must return true to
         *  skip the next guardzone check.
         *  Else return false.
         * *)
        method private queueChecks (skipCheck : bool)(currBoundsCheck : arrayOrPtr) 
                                            : bool  =

            begin
                match currBoundsCheck with
                |   Array(index, bounds) when skipCheck -> 
                            raise (Incorrect_Input "[queueChecks] Trying to skip an
                            array bounds check");

                (*  If the index bounds check goes through correctly, then we
                 *  return true to skip the next guardzone check (HOPEFULLY the
                 *  same check expressed as a guardzone check.)
                 *  Else if the bounds check fails, then return false to NOT
                 *  skip the next check.
                 * *)
                |   Array(index, bounds) -> 
                        begin
                            try (
                                (self#processArrayVar index bounds);
                                true
                            )
                            with
                            |   Not_an_Array -> false
                        end

                (*  In this case, we have been instructed to skip the guardzone
                 *  check because (presumably) the array bounds check was
                 *  completed successfully.
                 *  We are not gonna be skipping any check after a guardzone
                 *  check. We can only skip the check after a array bounds
                 *  check.
                 *  *)
                |   Dereference(addrPtr, derefValue, origValue) when skipCheck ->
                        false

                (*  We are not gonna be skipping any check after a guardzone
                 *  check. We can only skip the check after a array bounds
                 *  check.
                 *  *)
                |   Dereference(addrPtr, derefValue, origValue) -> 
                        begin
                            (self#processPtr addrPtr derefValue origValue);
                            false
                        end
            end

        (*  The basic objective of this method is pretty simple. it's simply to
         *  add the received parameter in the currExprList object. If the object
         *  is None, then we must pop the top statement of the stmtExprStack
         *  object.
         *  Else we simply add the received boundsCheck in the object.
         *
         *  HOWEVER, we must ensure that the boundsCheck we have received has
         *  not been added earlier.
         * *)
        method private enlistBoundsCheck (boundsCheck : arrayOrPtr) : unit =
            begin
                let (exprSource, exprList) = 
                    match currExprList with
                    |   None ->
                            let newExprList = (Stack.pop stmtExprStack)
                            in
                            begin
                                (currExprList <- Some(newExprList));
                                (newExprList.source, newExprList.exprList)
                            end
    
                    (*  We needn't do anything here *)
                    |   Some(storedResourcePair) -> 
                            (storedResourcePair.source,
                            storedResourcePair.exprList)
                in
                
                (*  Only if the current check does not exist in list, only then
                 *  do we add it to list. Note that we use structural equality
                 *  for the purpose.
                 * *)
                (*  Note that this feature has been commented out because the
                 *  hashing function was giving equality for expressions that
                 *  were obviously not equal. This was leading to elimination of
                 *  some checks.
                 * *)
                (*      if (not (List.exists 
                            (function currExpr -> 
                                (Hashtbl.hash currExpr) = (Hashtbl.hash boundsCheck))
                                exprList )) then 
                   *)
                    currExprList <-
                        Some({ 
                                source = exprSource;
                                exprList = (boundsCheck::exprList)
                            })
                
            end

         (*  The basic objective of this method is to finish off the processing
         *  for the current statement which is supplied as a parameter to the method.
         *  By "FINISH OFF", we mean queuing the current expressions in current
         *  list and having various checks to ensure that we do not have any
         *  incorrect processing.
         * *)

        method private stmtChecksProcessing (currStmt : stmt) : unit =
                begin
                    (*  The basic objective of this method is to ensure that IF
                     *  currExprList object contains SOME data, then it must be
                     *  that corresponding to the current statement being
                     *  processed.
                     * *)
                    let checkStmt (objSourcePair : exprSourcePair ) : bool =
                        match objSourcePair.source with

                        (*  Note that we are using structural equality here. We
                         *  might have to revisit this point later.
                         * *)
                        |   CurrStmt(objStmt) ->
                                    ((Hashtbl.hash objStmt) = (Hashtbl.hash currStmt))

                        (*  Note that if it's NOT the current statement, then it
                         *  basically means that it must belong to other
                         *  statement or instruction which is SIMPLY NOT
                         *  POSSIBLE.
                         * *)
                        |   CurrInstr(_) -> raise ( Incorrect_Input 
                        "[stmtChecksProcessing.checkStmt] was NOT expecting an instruction here." )

                    in
                    match currExprList with 
                    (*  This basically implies that we must pop the
                     *  stmtExprStack
                     * *)
                    |   None -> 
                        begin
                            (*  Note that we do not handle the Stack.Empty
                             *  exception here. There MUST be one element in the
                             *  table for every statement even if that statement
                             *  does not involve any expressions
                             * *)
                            let sourceElement, exprList =
                                    let topSourcePair = (Stack.pop
                                                stmtExprStack) 
                                    in
                                    match topSourcePair.source with
                                    |   CurrStmt(sourceStmt ) -> 
                                            ( sourceStmt,
                                            topSourcePair.exprList)

                                    |   _ -> raise (Incorrect_Input
                                        "[stmtChecksProcessing] Only statements
                                        can exist on the stack." )
                            in  

                            (*  Note that we cannot use structural equality with
                             *  recursive data structures and hence we will use
                             *  the hash function on the structures.
                             * *)
                            if ((Hashtbl.hash sourceElement) = (Hashtbl.hash currStmt)) then
                            begin
                                (*  Lets process the expressions that need to bounds
                                 *  checked or guardzone checked.
                                 *  Note that the first parameter is false to
                                 *  indicate that we do not want skip the first
                                 *  check.
                                 * *)
                                ignore (List.fold_left self#queueChecks false exprList);
                            end
                            else
                                raise ( Incorrect_Input "[stmtChecksProcessing]
                                Stack top was different from current
                                Instruction." )
                        end

                    (*  If the currExprList is NOT null, then it must contain
                     *  currStmt ONLY. It can neither contain any other
                     *  instruction OR any other statement
                     * *)
                    |  Some(currSourcePair) when (checkStmt currSourcePair) ->
                            begin
                                (*  Note that the first parameter is false to
                                 *  indicate that we do not want skip the first
                                 *  check.
                                 * *)
                                ignore 
                                (List.fold_left self#queueChecks false
                                        currSourcePair.exprList);

                                (*  Since we have done with the current
                                 *  statements processing, set the
                                 *  currSourcePair to None. Instructions should
                                 *  have finished their processing and other
                                 *  statements must have their list in the
                                 *  stmtExprMap.
                                 * *)
                                currExprList <- None
                            end
                    
                    |   _ -> raise ( Incorrect_Input "[stmtChecksProcessing] was
                    expecting a stmt here" )
                end

        (*  The basic objective of this method is to finish off the processing
         *  of the current instruction which is supplied as a parameter to the method.
         *  By "FINISH OFF", we mean queuing the current expressions in current
         *  list and having various checks to ensure that we do not have any
         *  incorrect processing.
         * *)
        method private instrChecksProcessing (currInstr : instr ) : unit =
                begin
                    let exprList = 
                        (*  Note that for an instruction, we really have NO option.
                         *  The currExprList MUST contain the currInstr or there has
                         *  been an error in processing.
                         * *)
                        match currExprList with

                        (*  Note that we are using structural equality here. We
                         *  might have to revisit this point later.
                         * *)
                        |   Some(sourcePair)  -> 
                                begin
                                match sourcePair.source with
                                |   CurrInstr (givenInstr) 
                                        when (
                                            (Hashtbl.hash givenInstr) = 
                                            (Hashtbl.hash currInstr)) ->
                                            sourcePair.exprList
                                
                                |   CurrInstr(_)  -> raise (Incorrect_Input
                                            "[instrChecksProcessing] Was
                                            expecting exactly the same
                                            instruction here")

                                |   _   -> raise (Incorrect_Input
                                            "[instrChecksProcessing] Was
                                            expecting an instruction and NOT a
                                            statement")
                                end

                        |  _ -> raise ( Incorrect_Input "[instrChecksProcessing]
                            Was expecting SOME data instead of NONE." )

                    in

                    begin
                        (*  Lets process the expressions that need to bounds
                         *  checked or guardzone checked.
                         * *)
                        (*  Note that the first parameter is false to
                         *  indicate that we do not want skip the first
                         *  check.
                         * *)
                        ignore  (List.fold_left self#queueChecks false exprList);

                        (*  Since we have done with the current
                         *  statements processing, set the
                         *  currSourcePair to None. Instructions should
                         *  have finished their processing and other
                         *  statements must have their list in the
                         *  stmtExprMap.
                        * *)
                        currExprList <- None
                    end
                end

        (*===================================================================*)
 
        (*  The basic objective of this method is to store the value of type
         *  C_Statement on statement_stack. *)    

        (*  The basic objective of this method is to filter out those uses of
         *  lval that are pointer expressions and then queue them up to be 
         *  processed at the end of statement.
         *
         *  Note that for every array bounds check, the corresponding guardzone
         *  check is added too, so that if the during array bounds processing
         *  later we realize that we do not have the array size, then we can
         *  just queue the guardzone check. If the processing succeeds, then we
         *  don't queue the guardzone check.
         *  *)

        method vlval (lValue : lval) : lval visitAction = 
        begin
            start_method ();
            log (class_name ++ text ".vlval : " );
            log (text "currLvalue:lval : " ++ (dn_lval () lValue));
            log unalign;

            (*  This method basically generates the correct dereference check
             *  based on whether the supplied lvalue can be dereferences or not.
             *  E.g., we cannot dereference and compare a structure value to a
             *  guardzone value. Neither can we do that with a function pointer.
             * *)
            let generateDerefCheck (currLval : lval) (castType : typ) : arrayOrPtr =
                (* The objective here is to first check if the supplied type
                 * can be dereferenced. If there is no way to dereference a
                 * pointer then compare it with a guardzone char value. Hence
                 * in that case, we change the type to Char pointer.
                 * *)
                match castType with
                    (*  For the following two types, we will need to convert
                     *  into character dereferences.
                     * *)
                    |  TComp(_,_)
                    |  TFun(_,_,_,_) -> 
                        
                        Dereference(                            
                        (*  Basically here we are converting the given pointer
                         *  into a character pointer and dereferencing it.
                         * *)
                            AddrOf(currLval),
                            Lval(Mem(CastE(Cil.uintPtrType, AddrOf(currLval))),
                                    NoOffset),
                            Lval(currLval)
                         )

                    |  _ ->  Dereference( AddrOf(currLval),
                                        CastE(castType, Lval(currLval)),
                                        Lval(currLval))

            (*  The basic objective of this method is to check if the current
             *  lvalue is actually a function pointer dereference. If it is,
             *  then there is no point in having a guardzone check for it, is it??
             * *)
            and is_function_ptr (currLval : lval) : bool =
                let lvalType = (Cil.typeOfLval currLval)
                in
                match lvalType with
                |   TFun(_,_,_,_) -> true
                |   _ -> false

            in

            (*  Check if the current lval is the right hand side of the set instruction AND
             *  if we are permitted to instrument it. 
             *  *)
            if (!instrReadsOnly && setLval ) then
                begin
                    (*  We are currently instrumenting only data-reads
                     *  operations which should theoretically NOT cost an extra
                     *  memory dereference.
                     * *)
                    setLval <- false;
                    SkipChildren
                end

            else
                begin
                    setLval <- false ;

            (*  The basic object here is to save the cast type into a local
             *  variable and then reset it.
             * *)
             (* Note that this field is important to us only in case of memory
              * dereference. We will basically ignore it for array indexing and
              * any other operation.
              * *)
             (* Note that this will always have a value because of either a cast
              * set earlier OR appended by us based on the current type of the
              * lval. We are gonna be analyzing the current type of lval because
              * although, e.g., unsigned char and signed char are of the same
              * size, the code generated is different. Hence it's important for
              * us to get the exact type of pointer.
              * *)
             let explicitType =
                     match currCastType with
                     |  None -> Cil.unrollTypeDeep (Cil.typeOfLval lValue)
                     |  Some(newType) -> (Cil.unrollTypeDeep newType)

             in

             begin
                currCastType <- None;
                
                (*  If currently instrumentation is turned off as indicated in
                 *  vstmt and vinstr functions then return without processing.
                 * *)
                if (not do_instrument) then
                        SkipChildren
                else
                    (*  The objective of these two methods is to check whether fields
                     *  being checked belong to a transformed variable  *)
                    let isTransField (field : fieldinfo) : bool =
                        ((field.fname = fld_front))(*  || (field.fname =
                            fld_rear))*)

                    (*  The objective of this method is to check whether the field being
                     *  accessed within a struct/union is a bitfield
                     * *)
                    and isBitField (currOffset : offset) : bool =
    
                        let checkForBitField (currOffset : offset) : bool =

                            (*  Note that a bit field must be last offset   *)
                            match currOffset with
                            |   Field(currField, NoOffset) ->
                                    if (currField.fname = Cil.missingFieldName) then
                                        true
                                    else 
                                        begin
                                            match (currField.fbitfield) with
                                            | Some (width) when (width > 0) -> true
                                            | _ -> false
                                        end
                            |   _ -> false
                        in

                        (*  Note that we must do the stripping because of accesses like 
                         *  header.tailer.zeroer.
                         *  What we basically aim to get is the last access in such a
                         *  string of accesses.
                         * *)
                        let rec stripOffset (currOffset : offset) : offset  = 
                            match currOffset with
                            |   Field(_, NoOffset) | Index(_, NoOffset) -> currOffset
                            |   Field(_, newOffset) | Index(_, newOffset) -> 
                                                ( stripOffset newOffset)
                            |   NoOffset -> currOffset
                
                        in
                        checkForBitField ( stripOffset (currOffset) )
                    in
                    begin
                        (*  If there was an address of operation immediately
                         *  before this lval reference, then what we have is an
                         *  address computation rather than a memory dereference.
                         *  Proceed to the children node without any action.
                         * *)
                        if (addressOfFlag) then
                            begin
                                (*  Reset the flag. It acts for only one level
                                 *  in the visitor tree structure
                                 * *)
                                addressOfFlag <- false;
                                DoChildren
                            end
                        else
                        match lValue with

                        (*  The first pattern is for fields of transformed variables,
                         *  gz_front and gz_rear. We would obviously not like these
                         *  fields to be guardzone-checked right? *)
                        |   (_, Field(currField, _ )) when (isTransField currField ) 
                                                -> SkipChildren

                        (*  The following two patterns below is matched when variable is 
                         *  1.  Is single-dimensional array with fixed size (either Static or dynamic or
                         *      no-length specified (extern array declaration)).   
                         *  2.  Is not an array within a struct.
                         *  Note that arrays with above two conditions met will be
                         *  termed as "safe" arrays.    
                        *)

                        (*  This pattern below works for simple arrays of the
                         *  transformed type.*)
                        |   (Var(currVar), Field(currField, Index( index,_))) 
                                        when (has_simple_array_acc lValue) ->
                                begin                    

                                   (self#enlistBoundsCheck
                                        (generateDerefCheck lValue explicitType)
                                    );

                                    (*  Note that we leave offset out of this business
                                    *  because an lval with an offset does not have
                                    *  array type rather the element-type of the array *)
                                    self#enlistBoundsCheck (Array((Var(currVar), Field(currField,
                                        NoOffset)), index));
                                    DoChildren
                                end
                        (*  Note that the following pattern works for simple arrays and
                         *  untransformed ones only. 
                         *  For global array variables, since global
                         *  variables are always transformed, they cannot confirm to
                         *  this case.
                         *  *)
                        |   (Var(currVar ), Index(index ,_ )) when (has_simple_array_acc lValue) ->
                                begin
                                   (self#enlistBoundsCheck
                                        (generateDerefCheck lValue explicitType)
                                    );
                                   (*  Note that we leave offset out of this business
                                    *  because an lval with an offset does not have
                                    *  array type rather the element-type of the array *)
                                    self#enlistBoundsCheck 
                                        (Array((Var(currVar), NoOffset), index));
                                    DoChildren
                                end

                        (*  This pattern is of lvals that use the Constructor Var, are
                         *  of array types, but failed to be recognized as a "safe"
                         *  array. These would need to be checked using guardzone checks. 
                         *  Note that these accesses MUST have offset as Index to
                         *  prevent an expression "array" in expression (array + 5) to
                         *  processed as an array-type reference.
                         *  *)
                        (*  This case also includes the one of an array access within a struct. 
                         *  The only case that we want to prevent is that of currVar being 
                         *  of array type, with NoOffset as the offset. *)
                        |   (Var(currVar), newOffset) when
                                            (has_array_access newOffset) ->
                                begin
                                   (self#enlistBoundsCheck
                                        (generateDerefCheck lValue explicitType)
                                    );
                                   DoChildren
                                end

                        (*  When type of current Lval is actually a function
                         *  invocation and is of the form of a pointer
                         *  dereference, then there is no point in actually
                         *  having a guardzone check for it, is it??
                         * *)
                        |   (Mem(_), _) when (is_function_ptr lValue) -> 
                                DoChildren

                        (*  The pattern below is for lvals that have the structure of
                         *  pointer dereference but are actually arrays and that too
                         *  ones with "safe" access.
                         *
                         *  Note that we want to concentrate only on pure expressions.
                         *  That is with NoOffset. Can't really explain it. 
                         *)
                 
                        |  (Mem(currExpr), NoOffset) when (self#isPtrArrayVar currExpr) ->
                                begin

                                    (*  The value arrayVar refers to (say) p in the
                                     *  expression *(p + 5 - x) 
                                     *)
                                    let arrayVar = self#getArrayFromExpr currExpr
                                    in

                                    (*  From eg currExpr = (array + 5 - x) then 
                                     *      index = ((array + 5 - x) - array)    
                                     *  Note that the type used here is an assumption :
                                     *  intType *)
                                    let arrayIndex = BinOp(MinusPI, currExpr,
                                                        (Lval(arrayVar)), intType)
                                    in

                                    begin
                                        (self#enlistBoundsCheck
                                            (generateDerefCheck lValue explicitType)
                                        );
                                       (*  Note that the lval supplied here must NOT be
                                        *  the lval that we are matching in the method
                                        *  but the pointer itself  *)
                                        self#enlistBoundsCheck
                                                (Array(arrayVar, arrayIndex));
                                        DoChildren
                                    end
                                end

                       (*  Here we are handling the case that we have a pointer
                            dereference of the syntax ptr->bit_field.
                            Since it's not possible to apply address-of operator to a
                            bitfield, we cannot apply the guardzone check in this case.
                        *)
                        | (Mem(currExpr), newOffset) 
                            when (isBitField(newOffset)) -> DoChildren

                        (*  Note that here we are ASSUMING that the expression has ptr/array
                         *  type. The decision we are trying to make is whether we should
                         *  use the function for char guardzone detection (single check) or
                         *  otherwise.
                         *  HENCE, if the expr is NOT even a pointer, then the right thing
                         *  to do is PROBABLY to just ignore this case.    *)
                        |   (Mem(_), _ ) ->
                                 begin
                                   (self#enlistBoundsCheck
                                        (generateDerefCheck lValue explicitType)
                                    );
                                    DoChildren
                                end

                       | _ ->  DoChildren
                    end  (*  corresponding begin in else part of doInstrument
                            condition *)

            end     (*  Corresponding to begin before currCastType assignment
                        statement   *)

                end (*  If condition for setLval    *)

        end     (*  Function end *)

        (*  The basic objective of this method is to get to very specific
         *  expression patterns and filter them out. 
         *  So far it's being coded more on a case-by-case basis and should be
         *  pretty limited hopefully    *)
        method vexpr (currExpr : exp) : exp visitAction =
        begin
            start_method ();
            log (class_name ++ text ".vexpr : ");
            log (text "currExpr:exp : " ++ (dn_exp () currExpr));
            log unalign;

            let parentCastType = currCastType 
            in

            begin
                currCastType <- None;

                (*  If currently instrumentation is turned off as indicated in
                 *  vstmt and vinstr functions then return without processing.
                 * *)
                if (not do_instrument) then
                    SkipChildren
                else
                    begin
                        match currExpr with

                        (*  The basic idea here is that Sizeof() is always evaluated by
                         *  the compiler statically and thus no pointer inside it will
                         *  be referenced anyway    
                         *  Basically even a null dereference works out fine, however
                         *  the null dereference gives a seg fault in the case of
                         *  guardzone check.
                         *  *)
                        |   SizeOf(_) -> SkipChildren
                        |   SizeOfE(currExp) -> SkipChildren

                        (*  Note that we currently want to suppress the evaluation of a
                         *  very specific expression e.g.,: &array[10]. We don't want the
                         *  evaluation of this expression because it is NOT a pointer
                         *  dereference *)
                        |   AddrOf(currLval) -> 
                                begin
                                    (*  IF we are processing child nodes
                                    *  then set the flag. I don't
                                    *  believe there is a need to set
                                    *  the flag in the above case when
                                    *  the children are skipped.
                                    * *)
                                    addressOfFlag <- true;
                                    DoChildren
                                end

                        (*  This condition corresponds to the case when we have a
                         *  pointer being assigned a value to the beginning of an array.
                         *  it's just a pointer assignment and not a dereference. So why
                         *  check it.   *)                     
                        |   StartOf(currLval) -> SkipChildren

                        |   CastE(castType, _ ) ->
                                begin
                                    (*  The objective is very simply to note
                                     *  that a cast was used. If this turns out
                                     *  to be a memory dereference, we will need
                                     *  to use this. Else just reset the object
                                     *  variable back to None.
                                     * *)
                                    (*  What if we have multiple casts
                                     *  ((int)((char)x)) ?? We will then
                                     *  consider ONLY the outermost cast..
                                     * *)
                                    ignore(
                                    match parentCastType with
                                    |   None -> 
                                            (currCastType <- Some(castType))

                                    (*  if some type has already been set by the
                                     *  outer expression, then we let it be and
                                     *  ignore the current one
                                     * *)
                                    |   Some(_) -> ()
                                    );
                                    DoChildren
                                end

                        (*  If the child expression is an lval, then retain
                         *  whatever casts were applied to it. This corresponds
                         *  to the case 
                         *   (Int * ) ((char * ) ptr)
                         *   In that case, ptr will be casted finally to Int *
                         *   However for the case
                         *   (Int * ) (ptr + 10), this scenario won't apply
                         *   because (Int * ) applies to binary op PlusPi and
                         *   not to the lval
                         * *)        
                        |   Lval(currLval) ->
                                begin
                                    currCastType <- parentCastType;
                                    DoChildren
                                end

                        |   _ -> DoChildren
                end
            end (*  Corresponding to begin with assignment to currentCastType *)
        end (*  Outermost begin *)

        (*  The objective of the current method is to filter out the functions
         *  that will be then instrumented. The other global variables will be
         *  ignored 
         *)
        method vglob (currGlob : global) : global list visitAction =

            (*  We do not want to transform any function that belongs to
             *  zcheck.h, for e.g.,: is_char_nonguard, right?   *)
            if (permitInstrumentation currGlob) then
                match currGlob with
                |   GFun(_ , _) -> DoChildren                        
                |   _   -> SkipChildren
            else
                SkipChildren

        (*  One more objective is to create the "abort variable" in each
         *  function.
         *)
        method vfunc (currFunc : fundec) : fundec visitAction =
            (*  Here we create the temp variable and assign it both
             *  to the function as well as the class variable
             *  *)
            let func_abort_var = (makeLocalVar currFunc
                                abort_var_name Cil.uintType   )

            (*  Here we retrieve the line ranges for the current
             *  function.
             *  *)
            and func_line_ranges = 
                            try (
                                Some(Hashtbl.find functions_list
                                       currFunc.svar.vname)
                            ) with
                            |   Not_found -> None
            in

            begin
                curr_abort_var <- func_abort_var;
                curr_line_ranges <- func_line_ranges;
                DoChildren
            end

        method vstmt (currStmt : stmt) :  stmt visitAction = 

        (*  it's basically a very simple method that basically invokes the method
         *  that finally enqueues all bounds checks that have been accumulated
         *  for the current statement.
         * *)
        let finishStmtProcessing (currStmt : stmt) : stmt =
            begin
                (self#stmtChecksProcessing currStmt);
                currStmt
            end

        in
        begin    
            (*  Lets get the processing of the currExprList out of the way
             * *)
            (self#enterStmt currStmt);

            match currStmt.skind with
            (*  For these two kinds of statements we do not have a single
             *  specific location
             * *)
            |   Instr(_)
            |   Block(_) -> ChangeDoChildrenPost(currStmt, finishStmtProcessing)

            (*  For the rest of statement types find the locations and then
             *  decide
             *)
            |   _  ->

                let currLocation = Cil.get_stmtLoc currStmt.skind 
                in

                (*  For statments which do not match our criteria, just
                 *  proceed ahead.
                 *  E.g.,: The statements/ parts of a function that we
                 *  specifically to be instrumented or NOT instrumented shall be
                 *  sorted out here.
                 * *)
                if (self#permit_element currLocation.line) then
                    begin
                        do_instrument <- true;
                         ChangeDoChildrenPost(currStmt, finishStmtProcessing)
                    end
                else
                    begin
                        (*  We must NOT instrument this current statement. Just that the
                         *  child statements may need to be instrumented
                         * *)
                        do_instrument <- false;

                        (*  Note that statements like for loops, while loops may lie
                         *  outside our range, yet their loops may lie within our line
                         *  range. Hence we must proceed to check those statements
                         * *)
                         ChangeDoChildrenPost(currStmt, finishStmtProcessing)
                    end
        end 

        (*  Note that we will have to "sanitize" instructions too to check which
         *  ones should be instrumented and which one should not be.
         * *)
        method vinst (currInstr : instr) : instr list visitAction = 
        (*  it's basically a very simple method that basically invokes the method
         *  that finally enqueues all bounds checks that have been accumulated
         *  for the current instruction.
         * *)
        let finishInstrProcessing (instrList : instr list) : instr list =
            begin
                (List.iter self#instrChecksProcessing instrList);
                instrList
            end

        in
        begin
            (*  Since we have entered a set instruction we would like to set
             *  the setLval flag to indicate that the next lval is the right
             *  hand side of the Set instruction.
             * *)
            ignore (

                match currInstr with
                |   Set(_,_,_) -> setLval <- true
                |   _ -> setLval <- false
            );

            (*  Lets get the processing of the currExprList out of the way
             * *)
            (self#enterInstr currInstr);

            let currLocation = Cil.get_instrLoc currInstr
            in

            (*  For instructions which do not match our criteria, just
             *  proceed ahead.
             *  E.g.,: The statements/ parts of a function that we
             *  specifically to be instrumented or NOT instrumented shall be
             *  sorted out here.
             * *)
             if (self#permit_element currLocation.line) then
                begin
                    do_instrument <- true;
                    (ChangeDoChildrenPost([currInstr], finishInstrProcessing))
                end
            else
                begin
                    do_instrument <- false;
                    (ChangeDoChildrenPost([currInstr], finishInstrProcessing))
                end
        end

        initializer
            begin
                is_char_guard.svar.vtype <- TFun(voidType, Some([("ptr", 
                        voidPtrType, [])]), false, []);

                is_data_guard.svar.vtype <- TFun(voidType, Some([("ptr",
                        voidPtrType, []); ("size", uintType, [])]), false, []);

                is_guard.svar.vtype <- TFun(voidType, Some([("ptr",
                        voidPtrType, []); ("size", uintType, [])]), false, []);

                is_array_acc_unsafe.svar.vtype <- TFun(voidType, Some([("index", 
                      uintType, []); ("arraySize", uintType, [])]), false, []);

                gz_abort.svar.vtype <- TFun(voidType, Some([("gz_abort_var",
                      uintType,[]) ] ), false, []);

           end
 
    end

(*  ======================================================================   *)

(*  The objective of this class is to provide methods that are useful for
 *  transforming variables. 
 *  *)
class virtual   transVisitor (f:file) 
                (initialVarTable : (varinfo, varinfo)Hashtbl.t)
                (initialTypTable : (typ)CTypeHashtbl.t  )
                (file_name : string) =
    object(self)
        inherit nopCilVisitor

        (*===================================================================*)
        (*  The first section of this class definition is to handle the 
         *  transformation of local variables and their definitions and their
         *  references *)

        (*  A Hashtable that stores the mapping between variables that have been
         *  guardzoned and their new structs.     *)
        val varReplacementTable = initialVarTable

        (*  A Hashtable that stores the mapping between types that have been
         *  transformed into guardzone structures.
         *  Note that this variable should be modified ONLY by
         *  transform_type method.
         *  Other methods may access in a read-only mode, but do not
         *  modify it as it may unnecessarily complicate debugging  *)
        val typReplacementTable = initialTypTable

        val mutable isSSUninitialized = false

        (*  Macros for initialization guardzones including the bitmap.
         * *)
        val init_both_guardzones            =  emptyFunction "init_both_guardzones" 
        val init_front_guardzone      =  emptyFunction "init_front_guardzone" 
        val init_rear_guardzone       =  emptyFunction "init_rear_guardzone"
        val uninit_both_guardzones          =  emptyFunction "uninit_both_guardzones"
        val uninit_front_guardzone    =  emptyFunction "uninit_front_guardzone"
        val uninit_rear_guardzone    =  emptyFunction "uninit_rear_guardzone"
        val uninit_superstruct_guardzone = emptyFunction "uninit_superstruct_guardzones"

        (*  Value used for logging  *)
        val curr_class_name = text "transVisitor"

        (*===================================================================*)
        (*  This section of the class will handle the initialization and 
         *  uninitialization of guardzones    *)

        (*  This method is used to create the calls to the macro for
         *  initializing the guardzone macros.
         *  This method is used for only function local variables.
         * *)
        method private func_init_guardzone (transLval : lval) : instr list =
            begin
               match transLval with
               (Var(vinfo),Field(fld,_)) -> begin
                start_method ();
                log (curr_class_name ++ text ".init_guardzone : ");
                log (text ("transLval:varinfo : " ^ vinfo.vname) );

                log unalign;

                let init_guardzone_call = 
                        Call(None, Lval((var init_front_guardzone.svar)),
                            [(Lval(transLval))], locUnknown)
                in
                begin
                    (*  The first element of the instruction list is the one to
                     *  initialize the size field of the transformed variable.
                     *  The orig_var must be unmarked.
                     *)
                    init_guardzone_call::[] 

                end
               end
              | (Var(transVar), NoOffset) -> begin
                start_method ();
                log (curr_class_name ++ text ".init_guardzone : ");
                log (text ("transVar:varinfo : " ^ transVar.vname) );
                log unalign;

                let orig_var_field = getVarField transVar var_field_name
                in

                let init_guardzone_call = 
                    if (is_incomplete_struct orig_var_field.ftype false) then
                        Call(None, Lval((var init_front_guardzone.svar)),
                            [(Lval(Cil.var transVar))], locUnknown)
                    else
                        Call(None, Lval((var init_front_guardzone.svar)),
                            [(Lval(Cil.var transVar))], locUnknown)
                in

                begin

                    (*  We have to go through this stunt every time this function
                     *  is called because init_guardzone is a macro and can take
                     *  arguments of any type.
                     * *)
                    init_front_guardzone.svar.vtype <- TFun(voidType, Some[("var",
                            transVar.vtype,[])], false, []);

                    (*  The first element of the instruction list is the one to
                     *  initialize the size field of the transformed variable.
                     *  The orig_var must be unmarked.
                     *)
                    init_guardzone_call::[] 
                    end
              end
              | _ -> raise (Incorrect_Input ("[func_init_guardzone] transLval is" ^
                            "a structure enclosing guardzoned fields"))
            end

        (*  Method to uninitialize the guardzones of a transformed variable *)
        method private func_uninit_guardzone (transLval : lval) : instr list =
            begin
                match transLval with
                (Var(vinfo),Field(fld,_)) ->
                 begin
                  if(not isSSUninitialized) then
                  begin
                  start_method ();
                  log (curr_class_name ++ text ".uninit_guardzone : ");
                  log (text ("transLval:varinfo : " ^  vinfo.vname));
                  log unalign;

                  let uninit_guardzone_call = 
                        Call(None, Lval((var uninit_front_guardzone.svar)),
                            [(Lval(Var(vinfo),Field(fld,NoOffset)))],
                            locUnknown)
                    
                        (*let ssvarlval = (Var(vinfo),NoOffset) in
                        Call(None, Lval((var uninit_superstruct_guardzone.svar)),
                        ([(Lval ssvarlval)]),
                        locUnknown)*)
                  in

                  begin
                    (*  We have to go through this stunt every time this function
                     *  is called because uninit_guardzone is a macro and can take
                     *  arguments of any type.
                     * *)
                    (*uninit_both_guardzones.svar.vtype <- TFun(voidType, Some[("var",
                        fld.ftype,[])], false, []);*)

                    isSSUninitialized <- false;
                    
                    uninit_guardzone_call::[]
                  end
                  end
                  else
                      []
                end
                | (Var(transVar),NoOffset) -> 
                    begin
                    start_method ();
                    log (curr_class_name ++ text ".uninit_guardzone : ");
                    log (text ("transVar:varinfo : " ^  transVar.vname));
                    log unalign;

                    let orig_var_field = getVarField transVar var_field_name
                    in
                    let uninit_guardzone_call = 
                      if (is_incomplete_struct orig_var_field.ftype false) then
                        Call(None, Lval((var uninit_front_guardzone.svar)),
                            [(Lval(Cil.var transVar))], locUnknown)
                      else
                        Call(None, Lval((var uninit_front_guardzone.svar)),
                            [(Lval(Cil.var transVar))], locUnknown)
                    in

                    begin
                    (*  We have to go through this stunt every time this function
                     *  is called because uninit_guardzone is a macro and can take
                     *  arguments of any type.
                     * *)
                    uninit_front_guardzone.svar.vtype <- TFun(voidType, Some[("var",
                        transVar.vtype,[])], false, []);
                    
                    uninit_guardzone_call::[]
                    end
                end    
                | _ -> raise (Incorrect_Input ("[func_init_guardzone] transLval is" ^
                            "a structure enclosing guardzoned fields"))
            end    

    (*  =================================================================  *) 
     end

(*  ======================================================================   *)

(*  The objective of this class is to process all the global elements in a file
 *  including functions.
 *  Note that this works on the premise that any global variable/function used
 *  in any function must have been defined before the function.
 *  We were forced into this unified way of handling functions and other global
 *  variables rather than doing it in two different sweeps is because some
 *  transformed types were being defined later in the file while they were being
 *  used earlier in functions.
 *   *)
class transformationVisitor     (f:file)              
                        (file_name : string) =
    object (self)

        (*=====================================================================*)
        (*  Variable definitions of previous globalVisitor class    *)

        (*  Here we pass an empty hash table to parent class for the typ_table
         *  and the var_table   *)
        inherit transVisitor f (Hashtbl.create 10) (CTypeHashtbl.create 10)
                                file_name as super
      
        (*  Value used for logging  *)
        val class_name = text "transformationVisitor"

        val varLvalMappingTbl = (Hashtbl.create 10)

        (*  This method returns our typReplacementTable. It will be needed in
         *  the next phase of our transformation    *)
        method get_typ_table = typReplacementTable

        (*  Names of functions used in the file for initializing and
         *  uninitializing guardzones. There are 3 such functions. One for array
         *  definitions, array declarations and one for the rest of the
         *  variables.
         *  *)
        val global_name_arr_defn =  file_name ^ suffix_array_defn
        val global_name_arr_decl =  file_name ^ suffix_array_decl
        val global_name_ptr_defn =  file_name ^ suffix_ptr_defn
        val global_name_default =  file_name ^ suffix_default

        (*  Now for the 3 functions that are gonna be doing the initialization.
         *  Note that their names must be the same as the name variables defined
         *  above.
         * *)
        val init_array_defn =  emptyFunction (file_name ^ suffix_array_defn )
        val init_array_decl =  emptyFunction (file_name ^suffix_array_decl)
        val init_ptr_defn =  emptyFunction (file_name ^ suffix_ptr_defn)
        val init_default =  emptyFunction (file_name ^ suffix_default)

        (*===================================================================*)
        (*  Variable definitions of previous functionVisitor class    *)

        (*  This list contains tuples of the form (oldVar, transVar). The
         *  difference between this list and previous hashtable is that the
         *  hashtable contains global variable mappings too while this list is
         *  function specific list  
         *  it's initialized at beginning of function processing and assigned
         *  empty list at the end of function processing    *)
        val mutable varMappingList = []

        val mutable main_file = false
        method is_main_file = main_file

        val mutable processing_function = false

        val mutable funcName = ref ""

        val mutable isIncompleteTransform = false

        val mutable type_instance_no = 0

        (*val isInCompleteTypeTbl = (Hashtbl.create 10)*)

        (*=====================================================================*)
        (*  Method definitions for handling global variables    *)

        (*  Note that the first argument here is an optional size variable. The
         *  size variable will exist when original variable is of type array or
         *  pointer.
         *  The first initialization is the transformed initialization (possibly
         *  no initialization at all)
         *  The instr lists correspond to :
             *  Array definitions with size and init info
             *  Array declarations. The one with size but NO initialization.
             *  Ptr definitions.
             *  Rest of the declarations + definitions
         *  *)
        method private transform_init   (transVar : varinfo)
                                        (currInit : initinfo) 
            : ( initinfo * Cil.instr list * Cil.instr list * 
                Cil.instr list * Cil.instr list) =

            (*  These fields are gonna be used every-where. Might as well get
             *  them here.
             *  Note that we cannot attempt getting rear-guardzone here because it
             *  might not exist in case of incomplete structures.
             *  *)
            let front_zone  = (getVarField transVar fld_front)
            and orig_var    = (getVarField transVar var_field_name)
            in

            (*  The objective of this very simple value is to see if the
             *  variable that has been passed to us, has already been
             *  initialized. If so, it returns true else false.
             *  *)
            let is_initialized    =
                    match currInit.init with
                    |   None -> false
                    |   Some(_) -> true

            (*  The basic objective of this method is:
                *  To determine if the original variable is an array definition
                *  If so, to return a initializer for the accompanying the
                *  transformed variable.
             *  Note that this method makes the assumption that supplied
             *  variable is a transformed variable that may or may not be an
             *  array definition.
             *  Note that in case of this NOT being an array definition, an
             *  expression with a value 0 is return.
             *  *)
            and is_array_with_size (transVar : varinfo) : (bool * exp) =     
                    let orig_var = (getVarField transVar var_field_name)
                    in
                            
                    match orig_var.ftype with
                    |   TArray(_, Some(arr_size_exp), _) ->
                                        (true, arr_size_exp)

                    |   _ -> (false, Const(CInt64((Int64.of_int 0), IUInt, None) ))

            (*  The basic objective of this method is to sanitize the init and
             *  generate the set of statements for correcting the extern
             *  variable references.
             * *)
            and sanitize_init (transLval: lval) (transInitInfo : initinfo)  
                                : instr list  =
            match transInitInfo.init with
            |   None -> []
            |   Some(transInit) ->
                begin
                    let generate_macro_call (targetLval : lval) 
                            (value : exp) : instr =
                    begin        
                        let macro = (emptyFunction "correct_struct_field")
                        and target_type = ( Cil.typeRemoveAttributes
                                            ["const"]
                                            (Cil.typeOfLval targetLval))
                        in
                    
                        let ptr_type = TPtr(target_type,[])
                        in

                        let ptr_type_expr = CastE(ptr_type, const_value_0)
                        in

                        begin
                            macro.svar.vtype <- TFun(voidType, 
                                    Some([  ("type_expr",ptr_type, []);
                                        ("var_name", target_type, []);
                                        ("value", (Cil.typeOf value), [])
                                        ])
                                    , false, []);
                    
                            Call(None, Lval(Cil.var macro.svar),
                                        [   ptr_type_expr;
                                            (Lval(targetLval));
                                            value
                                        ], 
                                    locUnknown)
                        end
                    end
                    in

                    let rec scan_init (lv: lval) (i: init) 
                            (acc: instr list) : instr list = 
                        begin
                            match i with 
                            |   SingleInit(currExp) ->
                                begin
                                (*  the objective here is to scan the expression to see if
                                 *  it contains anything of interest. If it does then we
                                 *  must isolate it and create the appropriate macro call.
                                 * *)
                                    let scanner = new expressionScanner 
                                                        varReplacementTable f
                                    in

                                    begin
                                        let sanitized_expr =
                                            (Cil.visitCilExpr (scanner :> cilVisitor) currExp)
                                        in

                                        (*  Lets check if the expression has a problem  *)
                                        if (scanner#is_exceptional_case) then
                                            let set_instr = 
                                                (generate_macro_call lv
                                                                        sanitized_expr)
                                            in

                                            (*  We add this to list of previous set
                                             *  instructions.
                                             * *)
                                            set_instr::acc
                                        else
                                            acc
                                    end
                                end
                            
                            |   CompoundInit (ct, initl) ->  
                                        Cil.foldLeftCompound ~implicit:false 
                                        ~doinit:(fun off' i' t' acc -> 
                                          scan_init (addOffsetLval off' lv) i' acc) 
                                        ~ct:ct ~initl:initl ~acc:acc
                        end
                        in

                        (scan_init transLval transInit [])
                end 

            (*  The basic objective is to modularize the initialization of the
             *  transformed variables.
             *  The third argument is set to true when an incomplete structure
             *  is being initialized. In that case, rear guardzone is not
             *  initialized.
             *  *)
            and init_trans_var  (transStruct : compinfo) 
                                (transInit : initinfo) 
                                (isIncomplete : bool) : initinfo =
                match transInit.init with
                |   None -> {init = None}
                |   Some(origInit) ->
                    begin
                        (*  Note that now we have two "kinds" of guardzones. The
                         *  ones of compact data-types: values which can fit
                         *  with 8/16 bytes and ones of structs larger than
                         *  compact types.
                         * *)
                        let sizeOfGuardCzone = 
                            let size = (Cil.constFold true (Cil.sizeOf
                                                front_zone.ftype))
                            in
                            match size with

                            (*  We have divided by 4 here because we need the
                             *  size of guardzone as number of unsigned integers
                             *  and not in bytes.
                             *
                             *  *)
                            |   Const(CInt64(value, _,_)) -> 
                                    ((Int64.to_int value)/4)
                            |   _ -> raise (Incorrect_Input ("Constant folding " ^
                                        " did not result in size of guardzone"))
                        in

                        (*  Creating the init for the front guardzone only.
                         *  We can create the rear guardzone only after
                         *  determining that the type is not incomplete.
                         *  *)
                        let front_zone_init = 
                            (Field(front_zone, NoOffset), (guardzone_init
                                                    sizeOfGuardCzone))

                        in
                        begin

                            let trans_var_init =  ((Field(orig_var, NoOffset), origInit))
                            in

                            if (isIncomplete) then
                                let trans_comp_init = (CompoundInit(transVar.vtype, 
                                    (front_zone_init :: trans_var_init ::  [])))
                            
                                in
                                {init = Some(trans_comp_init)}

                            else 

                                let trans_comp_init = 
                                try (
                                let rear_zone = (Cil.getCompField transStruct fld_rear)
                                in

                                let rear_zone_init = (Field(rear_zone, NoOffset), 
                                                        (guardzone_init sizeOfGuardCzone))
                                in

                                CompoundInit(transVar.vtype, 
                                (   front_zone_init :: trans_var_init ::  
                                    rear_zone_init ::[]))
                                ) with _ -> 
                                CompoundInit(transVar.vtype, 
                                (   front_zone_init :: trans_var_init ::  
                                 (*rear_zone_init ::*)[]))
                                in
                                
                                {init = Some(trans_comp_init)}
                        end
                    end
            
            (*  The objective of this method is to create the "call" instruction
             *  for the macro. Note that we are forced to have a method instead
             *  of directly defining an empty function for each macro because
             *  , since we are pretending that it's a function instead of a
             *  macro, the type of argument accepted by the "function" must be
             *  the "tweaked" to be the same as the variable that needs to be processed by
             *  the "function"
             *  *)
            and create_macro_call   (macro_name : string)
                                    (transVar : varinfo) 
                                    : instr =                                         
                let macro = emptyFunction macro_name
                in
                begin
                    macro.svar.vtype <- TFun(voidType, 
                        Some([("var_name", transVar.vtype, [])]), false, []);
                    
                    Call(None, Lval(Cil.var macro.svar),
                         [(Lval(Cil.var transVar))], locUnknown)
                end
            in

            let is_sized_array, array_size = (is_array_with_size transVar)
            and transformed_init = 
                match transVar.vtype with
                |   TComp(transStruct,_) ->
                        (init_trans_var transStruct currInit false )

                | _ -> raise (Incorrect_Input ("[transform_init] transformed" ^
                              " variable not a structure. Error."))
            in

            (*  The following statements constitute the sanitization of the init
             *  against references to extern variables that do not have their
             *  type completely defined.
             *  Note that we are still using currInit. Just that we have to give
             *  it the offset of orig_var
             * *)
            let sanitization_stmts =  
                (sanitize_init (Cil.var transVar) transformed_init)
            in

            match transVar.vtype with

            (***************************************************************)
            (*  First we will specifically deal with arrays *)

            (*  First and foremost, let us consider the case of an array
             *  declaration.    *)
            |   _ when (is_array_decl transVar) ->
                    (transformed_init, [], [], [], [])

            (*  Second we consider the case, where we have an array definition
             *  that has not been initialized.
             *  All the initialization will be done in the constructor.
             *  *)
            |   _ when ((not is_initialized) && is_sized_array) ->
                    
                    (*  We will call the macro here to perform the
                     *  initialization of various guardzones. This includes both
                     *  setting the values in the guardzones AND setting the
                     *  bitmaps too.
                     *  *)
                    let call_macro = (create_macro_call
                                "complete_init" transVar)

                    in
                    (transformed_init, [], call_macro :: sanitization_stmts
                            , [], [])

            (*  Let us take up the case of an array definition that has been
             *  initialized.
             *  In that case we use our modularized function that initializes
             *  transformed variables and initialize rear guardzones too.
             *  *)
            |   TComp(transStruct, _ ) when 
                        ((is_initialized) && is_sized_array) ->

                    (*  We will call the macro here to perform the
                     *  initialization of various guardzones in the bitmap
                     *  Note that in this case we call the partial macro.
                     *  *)
                    let call_macro = (create_macro_call "partial_init" transVar)

                    in
                    ( transformed_init, call_macro::sanitization_stmts, 
                        [], [], [] )

            (***************************************************************)
            (*  Here we will deal with structure definitions that are of
             *  incomplete type.
             *  Note that before this point we MUST take care of any missing
             *  structure definitions. The function is_incomplete_struct is VERY
             *  sensitive about it.
             *  *)
            |   TComp(transStruct, _ ) when ((is_incomplete_struct
                                                orig_var.ftype false ) 
                                            && is_initialized) ->

                    let call_macro = (create_macro_call
                                "front_partial_init" transVar)
                    in

                    (transformed_init,
                     [], [], [], call_macro::sanitization_stmts)

            (*  This case corresponds to the case of incomplete structure
             *  variable that has NOT been initialized.
             *  Note that even pointers have complete transformation.
             *  *)
            |   TComp(transStruct, _ ) when 
                            (is_incomplete_struct orig_var.ftype false) ->

                    (*  We will call the macro here to perform the
                     *  initialization of various guardzones. This includes both
                     *  setting the values in the guardzones AND setting the
                     *  bitmaps too.
                     *  *)
                    let call_macro = (create_macro_call
                                "front_complete_init" transVar)

                    in
                    (transformed_init, [], [], [], 
                        call_macro::sanitization_stmts )

            (***************************************************************)

            (*  Note that during initialization we have two cases: 
             *  1.  The variable by itself has initialization. In this case, we
             *      have to set the values of the guardzones during this
             *      initialization itself.
             *  2.  The variable does not have initialization. In that case we
             *      will do the complete initialization in the constructor
             *      function.
             * *)
            (*  Here we will handle the case when the variable does have some
             *  initialization.
             *  *)
            |   TComp(transStruct, _ ) when (is_initialized) ->
                    (*  We will call the macro here to perform the
                     *  initialization of various guardzones in the bitmap
                     *  Note that in this case we call the partial macro.
                     *  *)
                    let call_macro = (create_macro_call
                                "partial_init" transVar)

                    in
                    ( transformed_init, [], [], [], 
                        call_macro::sanitization_stmts)

            (*  This case corresponds to the case of Non-array
             *  variable that has NOT been initialized.
             *  Note that even pointers have complete transformation.
             *  *)
            |   TComp(transStruct, _ ) when (not is_initialized) ->
                    (*  We will call the macro here to perform the
                     *  initialization of various guardzones. This includes both
                     *  setting the values in the guardzones AND setting the
                     *  bitmaps too.
                     *  *)
                    let call_macro = (create_macro_call
                                "complete_init" transVar)

                    in
                    (transformed_init, [], [], [], 
                        call_macro::sanitization_stmts )

            |   _   -> raise (Incorrect_Input ("[transform_init] transformed" ^
                              " variable not a structure"))
            
        (*
         * Construct the field of the guard zone structure.
         *  It is also specified that the front and the rear
         *  guardzones should be aligned on 8 byte boundary
         *  Also remember than guard zones are treated
         *  as array of Uints.
         *)
        method private construct_field (name : string) (size : int) : (string *
        typ * int option * attributes * location) =
          (name, TArray(TInt(IUInt,[]),Some(Const(CInt64((Int64.of_int
          (size)), IUInt,None))), []), None, [(Attr("aligned", [AInt(8)]))],
          locUnknown)

        (*  The objective of this method is to determine if the specified type
         *  is a C type that can be transformed compactly. it's "CAN BE"
         *  transformed because we do not want to transform anything that does
         *  not fit within 8 bytes or 16 bytes. 
         *  With data types of size 8/16 bytes we can use the faster guardzone
         *  initialization macros.
         *  We also cannot transform functions, enums void etc.
         *  The result of this method is to create the fields of transformed
         *  structure.
         *)  
        method private transform_compact_types  (origVarType : typ) 
                                                (isGlobalType : bool)
                                                (isGlobalVar : bool) =

                (*  We seemed to be missing opportunities to use compact types
                 *  just because applications typedef common types like char and
                 *  stuff like 
                 * *)
                let  varType = (Cil.unrollTypeDeep origVarType)
                in

                match varType with
                |   TVoid(_)
                |   TFun(_, _, _, _)
                |   TBuiltin_va_list(_) 
                |   TNamed(_, _) -> raise (Incorrect_Input 
                    ("[transform_compact_types] Incorrect type being transformed."))

                (*  Note that we have a blanket rejection of all arrays and
                 *  structures. It is because at the global level we may have
                 *  only their declarations (in case of structures) and only the
                 *  declaration of the array(and not its size) thus making its
                 *  size of guardzone difficult to determine.
                 *
                 *  And it would be really screwy to maintain separate types for
                 *  global variables versus local variables.
                 * *)
                |   TArray(_,_,_)   -> (false, None)
                |   TComp(currCompInfo, _) when currCompInfo.cstruct -> (false, None)

                |   _ when ((sizeOfType varType) <= 16) ->
                        let trans_sixteen =
                                if(isGlobalVar) then
                                  let elemsize = (sizeOfType varType) in
                                  (* 
                                   * For non-array types, request size
                                   * is same as element size.
                                   *)
                                  let request_size = elemsize in
                                  let gz_size = (getRoundedRearGZSizeForGlobal elemsize
                                    request_size) in
                                  [
                                    (* 1st element: gz_front (front guardzone). 
                                     * Divide by 4 because guard zone is array
                                     * of unsigned ints. *)
                                    (self#construct_field fld_front (!frontGZSizeGlobal/4));

                                    (* 2nd element: the var to be embedded. The name of this
                                     * field will always be "orig_var". *)
                                    (var_field_name, varType, None, [], locUnknown);

                                    (* 3rd element: gz_rear (rear guardzone) *)
                                    (self#construct_field fld_rear (gz_size/4));
                                  ]

                               else
                                  let elemsize = (sizeOfType varType) in
                                  (* 
                                   * For non-array types, request size
                                   * is same as element size.
                                   *)
                                  let request_size = elemsize in
                                  let gz_size = (getRoundedGZSize elemsize
                                    request_size) in
                                  [
                                   (* 1st element: gz_front (front guardzone). *)
                                   (self#construct_field fld_front (gz_size/4));

                                   (* 2nd element: the var to be embedded. The name of this
                                    * field will always be "orig_var". *)
                                   (var_field_name, varType, None, [], locUnknown);

                                   (* We do not have rear guard zone for local
                                    * variables because of super struct
                                    * optimization. *)
                                  ]
                        in
                        (true, Some(trans_sixteen))

                |   _  -> (false, None)


        (*  Method to take the typ of the variable to be transformed and then
         *  embed into a structure guarded on flanks by the guardzones (buffers
         *  with preconfigured values.)
         *  Note that the parameter isInitialized refers to the fact that if the
         *  variable being transformed has been initialized or not.
         *  Note that we are again forced to make some distinctions between the
         *  way global variables and the way local variables are transformed
         *  because of concerns of efficiency of transformation.
         *  Lets list those concerns here.
         *  1.  In the perl benchmark lots of time is being consumed because of
         *      local buffers that are just 8 bytes but are being flanked by 24
         *      byte guardzones because of blanket rule about arrays.
         *
         *      Hence we will relax that rule in case of local variables because
         *      array size will ALWAYS be available in case of local variables.
         *  *)
        method private transform_type  (varType:typ) 
                                       (isGlobalType : bool )
                                       (isGlobalVar : bool)
                                       (suffix_string : string)
                                       (instance_no : int) : typ =
                let is_unsized_array_decl =
                        match varType with
                        |   TArray(_, None, _) -> true
                        | _ -> false

                (*  The first value is a flag that checks whether the supplied
                 *  varType can be embedded within either an 8 or 16 byte space.
                 *  The second contains the actual fields
                 * *)
                (*  Note that we use compact transformation ONLY if we are not
                 *  dealing with structures and arrays. This is because at a
                 *  global level we may not have the definition of a structure
                 *  or size of an array thus not allowing us to decide size of
                 *  guardzone in other files.
                 * *)
                and isCompactType, compactFieldsOption = 
                    if (is_fixed_type varType) then
                        (self#transform_compact_types varType isGlobalType
                        isGlobalVar)
                    else
                        (false, None)

                (*  Note that new naming convention of types is "gz_typ_" +
                 *  hash (varType). This is so that similarly named types
                 *  in different functions, and unnamed types may co-exist
                 *  peacefully at global level.
                 *  We earlier used Hashtbl.hash but it was colliding for
                 *  function pointers and hence we had to move onto this method. *)
                and sigString = Pretty.sprint 80 (d_typsig () (Cil.typeSig varType))

                in

                let typHash = 
                if(isGlobalVar) then
                  (Digest.to_hex (Digest.string sigString))
                else
                  (Digest.to_hex (Digest.string (sigString ^ "__" ^
                  (suffix_string) ^ "__" ^ (string_of_int instance_no))))

                and isArrayTypeWithKnownElementSize (vtype : typ) : bool =
                    match vtype with
                    TArray(elemtype,_,_) -> (Cil.isCompleteType
                    (Cil.unrollTypeDeep elemtype)) 
                    | _ -> false

                and getArrayElementSize (vtype : typ) : int =
                    match vtype with
                    TArray(elemtype,_,_) -> begin
                        match elemtype with
                        TArray(_,_,_) -> (!defaultGZSize)
                        | _ -> (sizeOfType elemtype)
                    end
                    | _ -> raise (Incorrect_Input ("Unexpected type"))

                in

                (*  This is the (string * typ * int option * attributes *
                 *  location) list that is needed by mkCompInfo.
                 *  *)
                let createFields (structure: compinfo) =
                    (*  If the variable is a global element,  then we would need
                     *  to differentiate between array and non-array variables.
                     *
                     *  Moreover, an array with size information would have the
                     *  rear guardzone within the struct, while for an array
                     *  without size information, this would not be possible.
                     *)

                    (*  Note that now for global variables we have introduced a
                     *  new field called gz_init. Basically this variable
                     *  indicates whether this variable has been initialized.
                     *  *)
                        match varType with

                        |   TBuiltin_va_list(_)
                        |   TNamed(_,_) 
                        |   TFun(_, _, _, _)
                        |   TVoid(_) -> raise (Incorrect_Input 
                                    ("[transform_type]Incorrect type being transformed."))

                         (*  Note that this partial transformation is valid in
                          *  very specific case
                          *  For GLOBAL arrays whose size has not been
                          *  specified. We can defined this kind of a structure
                          *  because the displacement of the orig_var from start
                          *  is fixed and unbounded arrays are allowed at the
                          *  end of the structure.
                          *
                          *  We are really not expecting this to be fulfilled
                          *  for function local variables
                          *  *)

                        |   _  when ( isGlobalType && is_unsized_array_decl)
                                -> begin
                            isIncompleteTransform <- true;

                            [
                             (* 1st element: gz_front (front guardzone) *)
                             (self#construct_field fld_front (!frontGZSizeGlobal/4));

                             (* 2nd element: the var to be embedded. The name of this
                              * field will always be "orig_var". *)
                             (var_field_name, varType, None, [], locUnknown);

                             (* For incomplete types, we cannot add guard zones
                              * on both sides otherwise the variable of that
                              * type cannot grow. *)
                            ]

                            end

                        (*  We definitely should not be having unsized arrays
                         *  in functions.
                         * *)
                        |   _  when ( is_unsized_array_decl) -> 
                                raise (Incorrect_Input 
                                    ("[transform_type] Unsized Array in" ^
                                        " function!!!."))
 
                        (*  This is specifically for the case of struct
                         *  declarations [NOT DEFINITIONS]. This is different from 
                         *  Incomplete structures because for incomplete structures, the
                         *  definition is known, just that it's incomplete.
                         *  Note that while isCompleteCheck can indicate an
                         *  unsize array too, we have already taken care of that
                         *  case above.
                         *  
                         *  We are NOT expecting this, because an incomplete
                         *  type can only have extern variable DECLARATION and we
                         *  should have handled this case right at variable
                         *  declaration stage.
                         * *)
                        |   _  when (isGlobalType && (not (Cil.isCompleteType varType))) -> 
                                    raise (Incorrect_Input 
                                        ("[transform_type] Wasnt " ^                              
                                         " expecting Incomplete types in type" ^
                                         " transformation"))
 

                        (*  This case corresponds very specifically to
                         *  incomplete structures. Note that the distinction of global
                         *  versus local is not made here. Because it's clearly
                         *  the case that C type system allows the structure to
                         *  be unbounded.
                         * *)  
                        |   _  when ( (is_incomplete_struct varType false))
                                -> 
                                    begin
                                      isIncompleteTransform <- true;

                            [
                            (* 1st element: gz_front (front guardzone) *)
                            (self#construct_field fld_front (!defaultGZSize/4));

                            (* 2nd element: the var to be embedded. The name of this
                             * field will always be "orig_var". *)
                            (var_field_name, varType, None, [], locUnknown);
                            ]
                       
                                    end
                        |   _ when isCompactType ->
                                begin
                                    match compactFieldsOption with
                                    |   Some(compactFields) -> compactFields
                                    |   None -> raise (Incorrect_Input 
                                            "Was expecting fields here.")
                                end

                        (* Handling local arrays of known size *)
                        |  _ when ((isArrayTypeWithKnownElementSize varType) &&
                                   (not isGlobalVar) &&
                                   (Cil.isCompleteType (Cil.unrollTypeDeep
                                   varType))) ->
                            let elemsize = (getArrayElementSize varType) in
                            let rounded_gzsize = (getRoundedGZSize elemsize
                            (sizeOfType varType)) in
                            
                            [
                             (*  1st element: gz_front (front guardzone). *)
                             (self#construct_field fld_front (rounded_gzsize/4));

                             (* 2nd element: the var to be embedded. The name of this
                             * field will always be "orig_var". *)
                             (var_field_name, varType, None, [], locUnknown);
                            ]

                        (* Handling global arrays of known size *)
                        |  _ when ((isArrayTypeWithKnownElementSize varType) &&
                                   (isGlobalVar) &&
                                   (Cil.isCompleteType (Cil.unrollTypeDeep
                                   varType))) ->
                            let elemsize = (getArrayElementSize varType) in
                            let rounded_gzsize = (getRoundedRearGZSizeForGlobal elemsize
                            (sizeOfType varType)) in
                            
                            [
                            (*  1st element: gz_front (front guardzone). *)
                            (self#construct_field fld_front (!frontGZSizeGlobal/4));

                            (* 2nd element: the var to be embedded. The name of this
                             * field will always be "orig_var". *)
                            (var_field_name, varType, None, [], locUnknown);

                            (* 3rd element: gz_rear (rear guardzone) *)
                            (self#construct_field fld_rear (rounded_gzsize/4));
                            ]

                        (* Handling all remaining types *)
                        |   _   ->

                            (* Globals *)
                            if (isGlobalVar) then
                             let elemsize = (sizeOfType varType) in
                             (* 
                              * For non-array types, request size
                              * is same as element size.
                              *)
                             let request_size = elemsize in
                             let gz_size = (getRoundedRearGZSizeForGlobal elemsize
                             request_size)
                             in

                             (* 
                              * For global composite types such as structures
                              * and unions, we cannot trust their size that
                              * we see in one translation unit, as it can 
                              * be defined with different size in another
                              * translation unit.
                              *)
                            [
                            (*  1st element: gz_front (front guardzone). *)
                            (self#construct_field fld_front (!frontGZSizeGlobal/4));

                            (* 2nd element: the var to be embedded. The name of this
                             * field will always be "orig_var". *)
                            (var_field_name, varType, None, [], locUnknown);

                            (* 3rd element: gz_rear (rear guardzone) *)
                            (self#construct_field fld_rear (gz_size/4));
                            ]
                            (* Locals *)
                            else
                              let elemsize = (sizeOfType varType) in
                              (* 
                               * For non-array types, request size
                               * is same as element size.
                               *)
                              let request_size = elemsize in
                              let gz_size = (getRoundedGZSize elemsize
                              request_size) in
                            [
                            (*  1st element: gz_front (front guardzone). *)
                            (self#construct_field fld_front (gz_size/4));

                            (* 2nd element: the var to be embedded. The name of this
                             * field will always be "orig_var". *)
                            (var_field_name, varType, None, [], locUnknown);
                            ]
                in

                let transCompinfo =  (mkCompInfo true (type_name_prefix ^
                                        typHash) createFields []) 
                in

                let transType = TComp(transCompinfo, [])
                in

                begin
                    (*  Add the type mapping to the global type table. Hence
                     *  forth, if a given type has been transformed, then
                     *  there would no need to transform it again   *)
                    isIncompleteTransform <- false;

                    if(isGlobalVar) then
                    CTypeHashtbl.add typReplacementTable 
                                (Cil.typeSig varType) transType;

                    if(isIncompleteTransform = true) then
                      Hashtbl.add isInCompleteTypeTbl transType 1;

                    transType
                end
           
        (*  This method basically transforms a list of variables. Note that all
         *  the variables in the list will be transformed.
         *  To this end it takes the function required to transform the variable
         *  as a parameter (createVar). This allows the method to process
         *  global, local and formal variables.
         *  The return is a tuple of (list of transformed variables, list of 
         *  global declarations of their type definitions)
         *  The transformed variables are needed for guardzone initialization and
         *  uninitialization.
         *  On top of it, the method examines each variable to see if it is
         *  array or pointer. If 
         *  If so, it creates another global uint variable with the
         *  name "gz_${var_name}_size".
         *  If the current global element is an array with length
         *  specified, the above created element is initialized to the
         *  size of the array.
        *
         *  *)
        method private global_transform_variables  (currVar : varinfo)
                                            (isInitialized : bool)
                                            (typeLoc : location) 
                                           : varinfo list * varinfo * global list =
                        
                (* Function to transform variables by using the new type from
                 * the typReplacementTable. *)
                let transformVar (oldVar : varinfo) : varinfo  = 
                        let baseTypeSig = (Cil.typeSig oldVar.vtype)
                        in
                        let transType =
                        try (
                            CTypeHashtbl.find typReplacementTable
                                            baseTypeSig
                          ) with
                          Not_found -> raise (Incorrect_Input ("var not found " ^
                          "in typeReplacementTbl " ^ oldVar.vname))
                        in
                        let transVar = 
                            (makeGlobalVar (var_name_prefix ^ oldVar.vname) 
                                transType)
                        in
                        begin
                            (*  This is critical as extern original variables must be
                             *  transformed into extern variables again *)
                            transVar.vstorage <- oldVar.vstorage;

                            (*  Note that we will also copy the attributes of
                             *  the original variable. 
                             *  This is experimental and may lead to some
                             *  problems
                             *  *)
                            transVar.vattr <- oldVar.vattr;

                            (*  Note that we might need to copy other oldVar
                             *  related data while transforming a variable  *)
                            transVar
                        end
                
                (*  The aim of the function is to check a variable and check its type
                 *  to see if it has been transformed and transform it if it has
                 *  not been done already.
                 *  The transformed type is added to the typReplacementTable.
                 *  The list of transformed types is returned back *)
                and transformVarType    (currVar : varinfo )
                                        (isInitialized : bool)
                                        : typ list =
                        (*  Extract the typsig of the type of the variable and 
                         *  transform the type if NEEDED. Else return an empty
                         *  list. 
                         *)
                            let oldTypeSig = (Cil.typeSig (unrollType
                                                    currVar.vtype))
                            in
                            if (CTypeHashtbl.mem typReplacementTable oldTypeSig) then
                                []
                            else
                              [(self#transform_type (unrollType currVar.vtype)
                               true currVar.vglob "global" 0)]
                        
                (* Function to create global declaration from type declaration *)
                and createDecl (transType : typ) : global  =
                        match transType with
                        | TComp (transComp, _ ) -> GCompTag(transComp, typeLoc)
                        | _ -> failwith "[createDecl] transformed type not a compinfo"
                in
                (*  Process the incoming variable to check if
                 *  variables type need transformation and transform them.
                 *  We use a list because the type may already have been
                 *  transformed so the list can be empty.
                 *  Note that we NEED the transformed type list to be
                 *  returned back   *)
                let transTypeList = (transformVarType currVar isInitialized)

                in
                (*  Transform the variable.   *)
                let transVar  = (transformVar currVar)
                (*  Note that the init variable is always created.
                 **)
                and init_var_list = [   ( makeGlobalVar
                                        (var_name_prefix ^ currVar.vname ^ var_init_suffix)
                                        (TInt(IUInt,[])))
                                    ]

                (*  We will define this variable per global variable only if
                 *  that variable is not of the fixed type.
                 * *)
                and ptr_var_list = 
                            if (not (is_fixed_type currVar.vtype)) then
                                [ makeGlobalVar
                                    (var_name_prefix ^ currVar.vname ^
                                    global_ptr_suffix)
                                    (TPtr(currVar.vtype, []))
                                ]
                            else
                                []
                in

                begin
                    (*  Adding the (oldVar, transVar) tuple to the
                     *  varReplacementTable   *)
                    (Hashtbl.add varReplacementTable currVar transVar);
                    ((ptr_var_list @ init_var_list), transVar, 
                        (List.map createDecl transTypeList ))
                end


         (*===================================================================*)
            
        (*  The basic objective of this method is to take a global variable
         *  (either a declaration or a definition) and search all the globals
         *  for the definition. 
         *  It returns back a definition of the variable OR the current declaration
         *  It also returns back a list of globals that are all declarations and/or
         *  definition of the same variable. This currently includes the first
         *  element too.
         *  The third result is the remaining list of globals.
         * *)
        method search_var_definition    (currGlobal : global)
                                        (globals : global list)
                                    :   (global * global list * global list) =
            begin

                (*  The objective of the method below is to check whether the
                 *  global element currently being considered is the same
                 *  variable that we are searching for.
                 *  *)
                let is_given_var    (currVar : varinfo)
                                    (newGlobal : global) : bool =
            
                    let are_types_same  (type1 : typ) 
                                        (type2 : typ) : bool = 

                        let calcTypeSig = (Cil.typeSigWithAttrs (fun x -> []))
                        and baseType1 = (unrollType type1)
                        and baseType2 = (unrollType type2)
                        in
                        (equals (calcTypeSig baseType1) (calcTypeSig baseType2))

                    in

                    match newGlobal with
                    |   GVar(newVar, _ ,_ ) | GVarDecl (newVar, _ ) ->
                            if (newVar.vname = currVar.vname ) then
                                (are_types_same newVar.vtype currVar.vtype)
                            else
                                false
                    |   _ -> false
                
                (*  A very simple method to just check whether the given
                 *  initinfo actually contains any initializing data.
                 * *)
                and isInitialized (givenInit : initinfo)  :  bool =
                    match givenInit.init with
                    |   Some (_) -> true
                    |   None -> false

                in
                
                match currGlobal with
                (*  The first case that we deal with is that the supplied global
                 *  element is the definition itself.
                 *  *)
                |   GVar(currVar, currInit, _ ) when (isInitialized currInit) ->
                        begin
                            let varDecls, globalList = 
                                List.partition (is_given_var currVar) globals
                            
                            in
                            (currGlobal, varDecls, globalList)
                        end

                (*  The second case is the one in which we are dealing with
                 *  a variable declaration.
                 *  *)
                |   GVar(currVar, _ , _) | GVarDecl(currVar, _) ->
                        begin
                            let varDecls, globalList = 
                                List.partition (is_given_var currVar)
                                globals
                            
                            and is_var_definition (currGlobal : global) : bool =
                                match currGlobal with
                                |   GVar(_, currInitInfo,_ ) when
                                        (isInitialized currInitInfo) -> true
                                | _ -> false
                            
                            in

                            let var_defn_list, var_decl_list  = 
                                (List.partition is_var_definition varDecls )

                            in

                            (*  This is the case where a variable definition
                             *  exists.
                             * *)
                            if ((List.length var_defn_list) > 0) then
                                
                                (*  Note that here we are banking on the fact
                                 *  that there cannot be more than one
                                 *  definition of a given variable.
                                 *  *)
                                ((List.nth var_defn_list 0), varDecls,
                                    globalList)                              
                            else
                            (*  If a variable definition does not exist then
                             *  just select the current variable declaration.
                             * *)
                                (currGlobal, varDecls, globalList)           
                        end

                (*  We cannot process any other global element and thus raise an
                 *  error.
                 *)
                |   _ -> raise (Incorrect_Input "[search_var_definition] Global
                element is neither a variable definition or a declaration" )

            end
                                
        (*=====================================================================*)
        (*  Method definitions for handling function transformations    *)

        (*  Check the variables to determine which need to be transformed *)
        (*  Note that the chkForArray var is a bool that specifies whether a 
         *  given variable should be checked for being an array that needs to be
         *  guardzoned.
         *  Note that not in all cases does this bool need be false. E.g., this 
         *  is true in case of formal variables, for only pointer are 
         *  passed as arguments to function call and NOT the entire array 
         *  itself   *)
        method private chkVar (chkForArray : bool) (oldVar : varinfo) : bool =       

                (*  Here we check if the variable is of type builtin_va_list. If
                 *  so we do not transform this variable. For some reason, its
                 *  vaddrof turned out to be in case of Perl benchmark function: 
                 *  Perl_dump_indent creating a problem for us. 
                 * *)
                match (Cil.unrollTypeDeep oldVar.vtype) with
                |   TBuiltin_va_list(_) -> false
                |   _ ->
                    (*  since in case of formal variables, arrays are passed
                     *  as pointers we must avoid transforming them.
                     *  PS: Not quite sure why I would write the following 
                     *  commented logic*)
                    (*  let safeArray = (is_simple_array oldVar.vtype) *)
                    if (chkForArray && (Cil.isArrayType oldVar.vtype)) then
                        false
                    else if (oldVar.vaddrof) then
                    (* We check if the type is SAFE as per CCured's analysis.
                     * If it is, then we don't transform the variable.
                     * If it is not, then we transform the variable
                     *)
                        try ( if(isSafeType oldVar.vattr) then
                            false
                             else
                            true
                        ) with _ -> false
                    else false


        (*  Function to create statements that will init a copy of formal 
         *  argument to the value of the formal argument. *)
        method private  initValue ((oldVar : varinfo),(transLval : lval))
                : stmt =
                match transLval with
                (Var(vinfo),Field(fld,off)) -> 
                    begin
               (*  Get the field named the oldVar in our transformed variable *)
                let varField = (getLvalField transLval var_field_name)
                in

                (*  Create an instruction to set the field of transformed 
                 *  variable with the value of the oldVar   *)
                let setInstr = Set((Var(vinfo), Field(fld, Field(varField,
                NoOffset))), Lval((Var(oldVar), NoOffset)), locUnknown)
                in

                (*  Transform the above Cil.instr into a Cil.stmt so that it 
                 *  can be "attached" to functions list of statements    *)
                mkStmtOneInstr setInstr
                    end
                | _ -> raise (Incorrect_Input ("Expecting transformed lval"))
 
        (* Function to perform post processing. Note that this has nothing to 
         * do with the list of globals that we receive as input. *)
        method private func_post_processing (currFunc : fundec)
                                            (initRzVar : stmt list)
                                            (globList : global list) 
                                            : global list  =
            begin
                start_method ();
                log (class_name ++ text ".func_post_processing : ");
                log (text ("currFunc:fundec : " ^ currFunc.svar.vname));
                log unalign;

                begin
                    let oldVarList, transVarList = List.split varMappingList 
                    in
                    begin
                        (*  Since this is the last method to be executed while
                         *  processing function, we must reset the object flag
                         * *)
                        processing_function <- false;

                        (*  "Attach" statements that init values of local copies
                         *  of formal parameters.
                         *  Note that this cannot be in vglob function as
                         *  reference to formal parameter is changed to transformed
                         *  local copy when children of currFunc node are
                         *  processed   *)
                        currFunc.sbody.bstmts <- initRzVar @currFunc.sbody.bstmts;

                        (*  removing the local variables mapping from the hashTable
                         *  . It still would contain mapping of global variables  *)
                        ignore(List.map (fun (oldVar:varinfo) -> Hashtbl.remove
                        varReplacementTable oldVar) oldVarList );
                    
                        (*  resetting the list  *)                        
                        varMappingList <-   [];
                        globList
                    end
                end

            end

        (*  This method basically transforms a list of variables. Note that all
         *  the variables in the list will be transformed.
         *  To this end it takes the function required to transform the variable
         *  as a parameter (createVar). This allows the method to process
         *  global, local and formal variables.
         *  The return is a tuple of (list of transformed variables, list of 
         *  global declarations of their type definitions)
         *  The transformed variables are needed for guardzone initialization and
         *  uninitialization.   *)
        method private function_transform_variables  (createVar : (string -> typ -> varinfo))
                                            (varList : varinfo list)
                                            (typeLoc : location)
                                            (fname : string)
                                           : varinfo list * global list =
                        
                (* Function to transform variables by using the new type from
                 * the typReplacementTable. *)
                let transformVar (oldVar,transType) : varinfo  = 
                        (*let baseTypeSig = (Cil.typeSig oldVar.vtype)
                        in
                        let transType = CTypeHashtbl.find typReplacementTable
                                            baseTypeSig
                        in*)
                        let transVar = 
                            (createVar (var_name_prefix ^ oldVar.vname) 
                                transType)
                        in
                        begin

                            (*  This is critical as extern original variables must be
                             *  transformed into extern variables again *)
                            transVar.vstorage <- oldVar.vstorage;

                            (*  Note that we will also copy the attributes of
                             *  the original variable. 
                             *  This is experimental and may lead to some
                             *  problems
                             *  *)
                            transVar.vattr <- oldVar.vattr;

                            (*  Note that we might need to copy other oldVar
                             *  related data while transforming a variable  *)
                            transVar
                        end
                
                (*  The aim of the function is to take a list of variables,
                 *  check their types to see which have been transformed and
                 *  then transform the types which have NOT been transformed
                 *  yet. The transformed types are added to the
                 *  typReplacementTable.
                 *  The list of transformed types is returned back. *)
                and transformVarTypes (varList : varinfo list) : typ list =

                        (*  Return the attributes of variable. Note that we need
                         *  two attributes of the variable. Its original type
                         *  AND whether it's a global variable or not
                         *  *)
                        let old_var_type (oldVar : varinfo) = (unrollType oldVar.vtype)

                        (*  Extract the typsig of the type of the variable and 
                         *  transform the type if NEEDED. Else return an empty
                         *  list. 
                         *) 
                        and transformGlobalType (oldType : typ) : typ list = 
                            let oldTypeSig = (Cil.typeSig oldType)
                            in
                            if (CTypeHashtbl.mem typReplacementTable oldTypeSig) then
                                []
                            else
                                [(self#transform_type oldType false true
                                "global" 0)]
                        and transformLocalType (oldType : typ) : typ list = 
                            (*let oldTypeSig = (Cil.typeSig oldType)
                            in
                            if (CTypeHashtbl.mem typReplacementTable oldTypeSig) then
                                []
                            else*)
                                begin
                                (type_instance_no <- type_instance_no + 1);
                                [(self#transform_type oldType false false fname type_instance_no)]
                                end
                        in

                        if((List.length varList) = 0) then
                        let old_var_type_list = (List.map old_var_type varList)
                        in
                        List.flatten (List.map transformGlobalType old_var_type_list)
                        else
                        let head = (List.hd varList) in
                        let old_var_type_list = (List.map old_var_type varList)
                        in
                        if(head.vglob = true) then
                          (*  Note that we get back from transformType is a list
                          *  that can be either empty or can contain exactly one
                          *  transformed type. List.map collates all such lists
                          *  into a List of lists. Hence List.flatten is needed.
                          *  *)
                          List.flatten (List.map transformGlobalType old_var_type_list)
                        else
                          (*  Note that we get back from transformType is a list
                          *  that can be either empty or can contain exactly one
                          *  transformed type. List.map collates all such lists
                          *  into a List of lists. Hence List.flatten is needed.
                          *  *)
                          List.flatten (List.map transformLocalType old_var_type_list)

                (* Function to add (oldVar, transVar) tuples to hashtable  *)
                and mapTransformation ((oldVar, transVar) : varinfo*varinfo )=
                    Hashtbl.add varReplacementTable oldVar transVar                            
                        
                (* Function to create global declaration from type declaration *)
                and createDecl (transType : typ) : global  =
                        match transType with
                        | TComp (transComp, _ ) -> GCompTag(transComp, typeLoc)
                        | _ -> failwith "[createDecl] transformed type not a compinfo"
                in
                begin
                    (*  Process the incoming list of variables to check which
                     *  variables types need transformation and transform them.
                     *  Note that we NEED the transformed type list to be
                     *  returned back   *)
                    let transTypeList = transformVarTypes varList in

                    (*  Create the list of transformed variables    *)

                    let transVarList  = (List.map transformVar (List.combine
                    varList transTypeList))
                    in
                    (*  Create a list of tuples of form (oldVar, transVar)
                     *  to added to the varReplacementTable *)
                    let transMapping = List.combine varList transVarList
                    in
                    (*  Adding the (oldVar, transVar) tuples to the
                     *  varReplacementTable   *)
                    List.iter mapTransformation transMapping;
                    (transVarList, List.map createDecl transTypeList )
                end

        (*=====================================================================*)
        (*  This section of the class contains all the methods of the
         *  nopCilVisitor class that have been over-ridden. These methods use
         *  the methods that have been defined in the previous sections of the
         *  class definition    *)

        method vglob (currGlob : global) : global list visitAction =
            (*  The basic objective of this function is to check if the function
                *  name supplied to us belongs to any one of the global variable
                *  guardzone initialization function
             * *)
            let is_init_function (name : string) : bool =
                (   (name = global_name_arr_defn) ||
                    (name = global_name_arr_decl) ||
                    (name = global_name_ptr_defn) ||
                    (name = global_name_default)
                )

            (*  The basic objective of this method is to determine if the local
             *  variables and formal arguments of the current function are to be 
             *  excluded from the transformation. This will be done in two
             *  cases.
             *  1.  In the exclusive instrumentation mode, then the functions
             *      name must NOT be in the functions_list hashtable
             *
             *  2.  In this exclusive NON-instrumentation mode, the function's
             *  name MUST be present AND no line ranges must have been mentioned. If
             *  that is the case, then no local variables or formal parameters
             *  need be transformed.
             * *)    
            and are_locals_excluded (func_name : string) : bool =

                (*  If locals are NOT to be transformed, then a separate switch
                 *  must be specified.
                 * *)
                if (!dontTransformLocals) then
                    (*  CASE 1.
                     * *)
                    if (!doInstrument ) then
                        begin
                            try (
                                let _ = (Hashtbl.find functions_list func_name)
                                in
                                false
                            ) with 
                            Not_found -> true
                        end
                    (*  CASE 2.
                     * *)
                    else
                        begin
                            try (
                                let line_ranges = (Hashtbl.find functions_list
                                                func_name)
                                in
                                ((List.length line_ranges) = 0)

                            ) with 
                            Not_found -> false
                        end
                else
                    false
            in
            begin
                start_method ();
                log (class_name ++ text ".vglob : ");
                log (text "currGlobal:global : " ++ (d_shortglobal () currGlob));
                log unalign;
                funcName := "";
                (Hashtbl.clear varLvalMappingTbl);
                isSSUninitialized <- false;
 
                if ((permitTransformation currGlob) && 
                    (permitInstrumentation currGlob)) then
                    match currGlob with

                    (*  One point to note from CIL documentation is GVar CANNOT
                     *  have extern declaration OR function type    
                     *  Note important point to note is that this is a variable
                     *  DEFINITION. Thus it must always have a concrete type as
                     *  opposed to variable declarations that can just have a
                     *  type declaration as opposed to type definition.
                     *  *)
                    |   GVar (origVar, origInitInfo, currLoc) ->

                        (*  This function checks whether the given var has been
                         *  defined as const and whether it has been referenced
                         *  using a pointer*)    
                        let fileOnlyVar (currVar : varinfo) : bool =
                            begin
                                match currVar.vstorage with
                                |   Static -> (not currVar.vaddrof)
                                |   _   -> false
                            end
                        in

                        (*  A small optimization that only the variable that can
                         *  can be externally referenced are transformed   
                         *  However we still need to visit init to see if any of
                         *  the initialization expressions need to be transformed 
                         *  in case it contains reference to any other global 
                         *  variable.
                         *  *)
                        if (fileOnlyVar origVar) then
                            DoChildren
                        else
                        begin
                            (*  Calling the search_var_definition method allows
                             *  us to pinpoint the exactly ONE
                             *  definition/declaration that we need to
                             *  transform. 
                             * *)
                            let currGlobal, decl_list, global_list  = 
                                ( self#search_var_definition currGlob f.globals )
                            
                            in

                            let currVar, currInitInfo  =       
                                match currGlobal with
                                |   GVar(var, varInitInfo, _) -> var, varInitInfo
                                |   GVarDecl(var, _ ) -> var, {init= None}
                                |   _ -> raise (Incorrect_Input
                                "[transformationVisitor.vglob] global element is NOT a
                                variable")
                            
                            in
                           (*   The extra_var_list currently refers to the init
                            *   variable that is created for each transformed
                            *   variable and possibly the ptr variable created
                            *   for arrays and structures.
                            * *)
                            let extra_var_list ,transVar, transTypeList = 
                                match currInitInfo.init with
                                |   Some(_) ->
                                    (self#global_transform_variables currVar true currLoc)
                                |   None ->
                                    (self#global_transform_variables currVar false currLoc)

                            in
                            begin

                                (*  Basically removing all the declarations
                                 *  + definition pertaining to the current
                                 *  untransformed
                                 *  global  element from
                                 *  the list of global elements *)
                                f.globals <- global_list;
       
                                (*  An extremely subtle but important point to
                                 *  note is that since global variables are
                                 *  being transformed first, we might have a new
                                 *  transformed type that is used in both a
                                 *  function variable and a global variable, and
                                 *  then global variable comes after the
                                 *  function.
                                 *  Since the transformed type definition will
                                 *  be needed by the function variable as well,
                                 *  we will need to put the transformed type
                                 *  before its first need.
                                 * *)

                                (*  Lets carry out the initialization of the
                                 *  variable.
                                 *  That should return to us the various
                                 *  instructions to initialize guardzone in
                                 *  various different initialization functions.
                                 * *)
                                let  transInitInfo, array_defn, array_decl,
                                        ptr_defn, default_init =
                                            (self#transform_init transVar currInitInfo)
                                
                               in
                               let globalTransVar = GVar(transVar, transInitInfo,
                                                                currLoc)
                               and array_defn_stmt = List.map
                                                     mkStmtOneInstr array_defn
                               and array_decl_stmt = List.map
                                                     mkStmtOneInstr array_decl
                               and ptr_defn_stmt  = List.map
                                                     mkStmtOneInstr ptr_defn
                               and default_init_stmt = List.map
                                                     mkStmtOneInstr default_init
                               
                               in

                               begin
                                    (*  "Attaching" the guardzone initilization
                                     *  statements to the various global
                                     *  initialization functions.
                                     *  Note that some of these lists may be
                                     *  empty depending upon the type of the
                                     *  variable and initialization.
                                     *  *)
                                    init_array_defn.sbody.bstmts <-
                                        array_defn_stmt @ init_array_defn.sbody.bstmts;

                                    init_array_decl.sbody.bstmts <-
                                        array_decl_stmt @ init_array_decl.sbody.bstmts;
                                    
                                    init_ptr_defn.sbody.bstmts <-
                                        ptr_defn_stmt @ init_ptr_defn.sbody.bstmts;
                                    
                                    init_default.sbody.bstmts <-
                                        default_init_stmt @ init_default.sbody.bstmts;

                                    let createDecl (currVar : varinfo):global =
                                                GVarDecl(currVar, currLoc)

                                    in

                                    (*  Changing the current global variable to
                                     *  transformed variable and transformed type.
                                     *  Note that transTypeList MAY be empty. 
                                     *  Note that here we have included the size
                                     *  variable and init variable
                                     *  declarations too
                                     *  *)
                                    ChangeDoChildrenPost(  transTypeList @
                                                            (List.map createDecl
                                                            extra_var_list) @
                                                            [globalTransVar]
                                                            , function x -> x)
 
                                end
                            end
                        end
                
                    (*  Process variable declarations. Note that function
                     *  prototypes also count as variable declarations and hence
                     *  must be adequately avoided.
                     *  An extremely important point from CIL documentation is
                     *  that a variable declaration has EITHER a variable
                     *  definition later OR an extern storage qualifier.
                     *  *)
                    |   GVarDecl (origVar, currLoc) when (not (isFunctionType
                                                    origVar.vtype))-> 
                            (*  Calling the search_var_definition method allows
                             *  us to pinpoint the exactly ONE
                             *  definition/declaration that we need to
                             *  transform. 
                             * *)
                            let currGlobal, decl_list, global_list  = 
                                 ( self#search_var_definition currGlob f.globals )
                            in

                            let currVar  =       
                                match currGlobal with
                                |   GVar(var, _, _) | GVarDecl(var, _ ) ->
                                        var
                                |   _ -> raise (Incorrect_Input
                                    ("[transformationVisitor.vglob] global" ^
                                    " element is NOT a variable"))
                            in

                            (*  Note that we distinguish between variable
                             *  declarations with structure declarations versus
                             *  those variable declarations whose structures are
                             *  completely defined. 
                             *  For variables with structure declarations ONLY,
                             *  the only use is to pass their pointers around.
                             *  Hence in varTransformationTable we will have the
                             *  Dereferenced pointer to this variable.
                             * *)
                            if (not ( is_type_defined currVar.vtype) ) then
                                begin
                                    let var_ptr_type = TPtr(currVar.vtype, [])
                                    in

                                    let var_ptr = 
                                            ( Cil.makeGlobalVar
                                                (var_name_prefix ^ currVar.vname ^
                                                global_ptr_suffix)
                                                var_ptr_type
                                            )
                                    in

                                    let var_ptr_decl = GVarDecl(var_ptr, currLoc)
                                    in

                                    begin
                                        (*  Now we insert this substituted
                                         *  variable declaration in the
                                         *  varTransformationTable.
                                         * *)
                                        (Hashtbl.add varReplacementTable currVar 
                                                var_ptr);
                                        ChangeDoChildrenPost( [var_ptr_decl] 
                                                        , function x -> x)
                                    end
                                end
                            else
                            begin
                                 (*  Note that the transTypeList MAY BE EMPTY
                                 *  depending upon whether the original type had
                                 *  been transformed earlier or not *)
                                let extra_var_list, transVar, transTypeList =
                                    (self#global_transform_variables currVar false currLoc)
                                in

                                let transVarDecl = GVarDecl(transVar,
                                                            currLoc)
                                in

                                begin
                                    (*  Basically removing the transformed global
                                     *  from the list of global elements *)
                                    f.globals <- global_list;
            
                                    let createDecl (currVar : varinfo):global =
                                                GVarDecl(currVar, currLoc)

                                    in

                                    (*  Changing the current global variable to
                                     *  transformed variable and transformed type.
                                     *  Note that transTypeList MAY be empty.  
                                     *  Note that declaratation for init
                                     *  variable is included too.
                                     *  *)
                                    ChangeDoChildrenPost( transTypeList @ 
                                                        (List.map createDecl
                                                        extra_var_list) @
                                                        [transVarDecl] 
                                                        , function x -> x)
                                end
                            end

                (*  Note that we do not wanna instrument the global
                 *  initialization functions.
                 *)
                |   GFun (currFunc, funcLoc) 
                            when ((not (is_init_function currFunc.svar.vname))
                            
                            (*  MOREOVER, we check to see if there is any need
                             *  to transform local variables and formal
                             *  variables. Do note that global variables have
                             *  still been transformed and their access in the
                             *  current function will need to changed
                             * *)
                            && (are_locals_excluded currFunc.svar.vname)) ->

                        begin
                            log (text ("Local variables to be untransformed in function: " 
                            ^ currFunc.svar.vname));

                            funcName := currFunc.svar.vname;

                            if currFunc.svar.vname = "main" then
                                ignore(main_file <- true);

                            (*  Set the object flag indicating that we are
                            *  processing functions
                            * *)
                            processing_function <- true;
                            ChangeDoChildrenPost([currGlob] , 
								function globList -> 
									begin
										processing_function <- false;
										globList
									end									
							)
                        end

                (*  Note that we do not wanna instrument the global
                 *  initialization functions.
                 *)
                |   GFun (currFunc, funcLoc) when not ( 
                                    (is_init_function currFunc.svar.vname)) ->
                                       
                        (*  The objective of this function is to conditionally
                         *  generate the instruction for calling the
                         *  ensure_sframe_bitmap function. This function should
                         *  be called only when there are transformed variables
                         *  in a given function. Not otherwise.
                         *  
                         * *)
                        let call_sframe_func (count : int) : instr list =
                            let sframe_func =  emptyFunction
                                            "ensure_sframe_guard_map" 
                            in
                            let func_call_instr = 
                                    Call(None, Lval((Cil.var sframe_func.svar)),
                                    [], locUnknown)
                            in
                            begin
                                sframe_func.svar.vtype <- TFun(voidType, None,
                                false, []);
                                if (count != 0) then
                                    [func_call_instr]
                                else
                                    []
                            end
                        in

                        (*
                         * This function takes a list of all transformed
                         * guardzoned variables and puts them inside a single
                         * struct and returns corresponding lvalues for original
                         * variable and the big structure variable.
                         *)
                        let putAllVarsInOneStruct(transVarList : varinfo list)
                        (fname : string) : (varinfo * compinfo * ((lval list) *
                        (varinfo list))) = 

                          let getGZSize (t : typ) : exp =
                            match t with
                            TComp(cinfo,_) -> begin
                              if((List.length cinfo.cfields) = 0) then
                                raise (Incorrect_Input 
                                ("Invalid no of fields in transformed var"))
                              else
                                          let gzfld = (List.nth cinfo.cfields 0)
                                          in
                                          begin
                                          (* This should be front guardzone *)
                                          match gzfld.ftype with
                                          TArray(_,Some(e),_) -> e
                                          | _ -> raise (Incorrect_Input 
                                          ("Invalid type of front guardzone"))
                                          end
                                      end
                                      | _ -> raise (Incorrect_Input 
                                      ("Invalid type of transformed var"))
                          in

                          let getFieldInfosList (structure : compinfo) :
                              (string * typ * int option * attributes *
                              location) list =

                              let rec filterIncompleteStruct (varlist : varinfo
                              list) : varinfo list =
                              match varlist with
                                v::vs -> if(is_incomplete_struct v.vtype false)
                                         then (filterIncompleteStruct vs)
                                         else ([v]@(filterIncompleteStruct vs))
                                | [] -> []
                              in

                              let sortAndProcessGZVars (varlist : varinfo list)
                              : varinfo list =

                                  let rec compare_varinfo (v1 : varinfo) (v2 :
                                      varinfo) : int =
                                    let gz_size1 = (getGZSize (v1.vtype)) in
                                    let gz_size2 = (getGZSize (v2.vtype)) in
                                     if (gz_size1 = gz_size2) then 0
                                     else if (gz_size1 > gz_size2) then 1
                                     else -1
                                  in

                                  (List.sort compare_varinfo varlist)
                              in

                              let rec createFieldInfoAttrsList(transVarList :
                                  varinfo list) : (string * typ * int option *
                                  attributes * location) list =
                                match transVarList with
                                v::vs -> let retList = 
                                         [(v.vname, v.vtype, None, v.vattr,locUnknown)] in 
                                         retList @(createFieldInfoAttrsList vs)
                                | [] -> []
                              in

                              if(not ((List.length transVarList) = 0))
                              then
                                begin
                                  let noIncompleteStructList = (filterIncompleteStruct transVarList) in
                                  let sortedGZSizeList = (sortAndProcessGZVars
                                  noIncompleteStructList) in
                                  let gz_ss_rear_var = 
                                    let len = (List.length sortedGZSizeList) in
                                    let lvar = (List.nth sortedGZSizeList
                                    (len-1)) in
                                    (* Size of rear guardzone is same as that of
                                     * largest size of guardzone of a variable 
                                     *)
                                    let greatest_gzsize = (getGZSize lvar.vtype) in
                                      (fld_rear, 
                                      TArray(TInt(IUInt,[]),Some(greatest_gzsize),[]), 
                                      None,  [(Attr("aligned", [AInt(8)]))], locUnknown)
                                  in
                                  let fldInfoAttrsList = (createFieldInfoAttrsList
                                  sortedGZSizeList)in 
                                    (fldInfoAttrsList @ [gz_ss_rear_var])
                                end
                              else
                                  []
                          in

                          let sscompinfo = 
                              (Cil.mkCompInfo true ("__" ^ fname ^ "__SuperStruct") 
                              getFieldInfosList []) 
                          in

                          let ssvar = 
                              (Cil.makeVarinfo false "__SS__"
                              (TComp(sscompinfo,[]))) 
                          in

                          let rec getFieldLvalList (ssvar : varinfo)
                          (transVarList : varinfo list) (unaffectedTransVars :
                              varinfo list): lval list * varinfo list =

                              let rec getFieldInfo (tvName : string) (flds :
                                  fieldinfo list) : fieldinfo =
                                match flds with
                                f::fs -> if(f.fname = tvName) then
                                          f
                                         else
                                          (getFieldInfo tvName fs)
                                | [] -> raise (Incorrect_Input("[getFieldInfo]" ^
                                               "variable not a field in a" ^
                                               "structure"))
                              in

                              match transVarList with
                              v::vs -> let nlval,uatVarList = if(is_incomplete_struct v.vtype false)
                                       then (Var(v),NoOffset), ([v])
                                       else
                                        let fld = 
                                          (getFieldInfo v.vname sscompinfo.cfields) 
                                        in
                                        ((Var(ssvar),Field(fld,NoOffset)),[])
                                        in
                                        let ll,vl = (getFieldLvalList ssvar vs
                                        unaffectedTransVars) in
                                        (([nlval] @ ll), (uatVarList @ vl))
                              | [] -> ([],[])
                           in

                           (ssvar, sscompinfo, (getFieldLvalList ssvar
                           transVarList []) )
                        in

                        let rec convertVarsInLvalList (transVarList : varinfo list)
                        : lval list =
                            let convertVarInLval (transVar : varinfo) : lval =
                                (Var(transVar),NoOffset)
                            in
                            match transVarList with
                            v::vs -> [(convertVarInLval v)] @ 
                            (convertVarsInLvalList vs)
                            | [] -> []
                        in

                        let rec populate_varLvalMappingTbl (origVarList :
                            varinfo list) (transLvalList : lval list) : unit =
                            match origVarList,transLvalList with
                              ((v::vs),(l::ls)) -> 
                                  begin
                                      match l with
                                      (Var(_),NoOffset) ->
                                          (populate_varLvalMappingTbl vs ls);
                                      | (Var(_),Field(_,_)) ->
                                        begin
                                      (Hashtbl.add varLvalMappingTbl v l);
                                      (populate_varLvalMappingTbl vs ls);
                                        end
                                      | _ -> raise (Incorrect_Input ("Strange" ^
                                             "value is being transformed" ))
                                  end
                              | ([],[]) -> ()
                              | ([],_) | (_,[]) -> 
                                      raise (Incorrect_Input ("Expecting" ^
                                      " both lists of same length"))
                        in

                    begin
                        if currFunc.svar.vname = "main" then
                            ignore(main_file <- true);

                        (*  Set the object flag indicating that we are
                         *  processing functions
                         * *)
                        processing_function <- true;

                        funcName := currFunc.svar.vname;

                        type_instance_no <- 0;

                        (*  Creating a local function as a partial application
                         *  to function function_transform_variables.
                         *  The basic idea is to "customize"
                         *  self#function_transform_variables.*)
                        let  transform_locals = (self#function_transform_variables
                                (makeLocalVar currFunc ))
                        in

                        (*  Selecting which formal and local variables must be
                         *  transformed.
                         *  Note that we get the list of untransformed local
                         *  variables because we need to remove the original
                         *  versions of transformed local variables.    *)
                        let chosenLocalVar, unaffectedLocalVar 
                            = (List.partition (self#chkVar false) currFunc.slocals)
                        and chosenFormalVar = (List.filter (self#chkVar true) 
                                                currFunc.sformals)
                        in

                        (*  Transforming the local variables which have been
                         *  operated on by & operator   *)
                        let transVarLocals, localDecl  = ( transform_locals 
                                chosenLocalVar funcLoc currFunc.svar.vname)
                        (*  Transforming the formal parameters which have been
                         *  operated on by & operator   *)
                        and transVarFormals, formalDecl = (transform_locals
                                chosenFormalVar funcLoc currFunc.svar.vname)
                        in

                        (*  Sequence of instructions to assign to object value
                         *  varMappingList *)
                        let oldVarList = chosenLocalVar @ chosenFormalVar
                        and transVarList = (transVarLocals @ transVarFormals)
                        in
                        let (_,_,(transLvalFormals,_)) = (putAllVarsInOneStruct
                        transVarFormals currFunc.svar.vname) 
                        and
                        (ssvar,sscompinfo,(transLvalList,unaffectedTransVars)) = 
                            (putAllVarsInOneStruct transVarList currFunc.svar.vname)
                        in
                        let ssvar_gtype = (GCompTag(sscompinfo,locUnknown))
                        in
                        (*  Create a list of tuples of form (oldVar, transVar)
                         *  to added to the varReplacementTable *)
                        let transMapping = List.combine oldVarList transLvalList
                        in
                        (*  Assigning the list to the object to be used during
                         *  uninitialization of guardzone *)
                        varMappingList <- transMapping;

                        (*  Creating a list of instructions for initialization
                         *  the guardzones of the transformed variables   *)
                        let initGuardCzonesInstr1 = 
                        (* If the function is to be excluded from initialization
                         * *)
                        if(isFuncExcludedFromInitUninit currFunc.svar.vname
                        !iufunctions_list) then
                            []
                        else
                            List.flatten (List.map
                            self#func_init_guardzone (transLvalList))
                        in

                        let initGuardCzonesInstr =
                        if(not ((List.length sscompinfo.cfields) = 0)) then
                        (*let nfields = (List.length sscompinfo.cfields) in
                        let last_field_lval = (Var(ssvar), (Field((List.nth
                        sscompinfo.cfields (nfields-1)), NoOffset))) in
                        let init_last_field = 
                        Call(None, Lval((var init_rear_guardzone.svar)),
                            [(Lval(last_field_lval))], locUnknown) in*)
                        let last_field_lval = (Var(ssvar),NoOffset) in
                        let init_last_field = 
                        Call(None, Lval((var init_rear_guardzone.svar)),
                            [(Lval(last_field_lval))], locUnknown) in
                        (initGuardCzonesInstr1 @ [init_last_field])
                        else
                          initGuardCzonesInstr1

                        (*  Combining the formal parameters and their transformed
                         *  variables into a single list. Needed later  *)
                        and formalVarMap = (List.combine chosenFormalVar
                        transLvalFormals)

                        (*  Creating statements to call the ensure_sframe_guard_map
                         *  function. This function ensures that the pages in
                         *  the bitmap corresponding to stack page frames are
                         *  allocated for.
                         *  Note that although the return type of the function
                         *  is a list, it's either a list containing one element
                         *  or an empty list. The list just makes things easy to
                         *  work with.
                         *  *)
                        and sframeCallInstr = 
                            if(isFuncExcludedFromInitUninit currFunc.svar.vname
                                !iufunctions_list) then
                                    []
                            else
                            call_sframe_func 
                                (List.length (transVarLocals @
                                transVarFormals))
                        in

                        (*  From instructions we need to convert to statements
                         *  so that we can "attach" them to start of the
                         *  function body   *)
                        let initGuardCzonesStmts = (List.map mkStmtOneInstr
                            initGuardCzonesInstr )
                        (*  Creating a list of statements that would init the
                         *  local copies of formal parameters   *)
                        and initFormalVar = (List.map self#initValue formalVarMap)
                        and sframeCallStmt = (List.map mkStmtOneInstr
                                                sframeCallInstr )

                        in
                        begin
                            (*  Creating a new list of local variables by
                             *  concatenating the list of untransformed local
                             *  variables and new transformed variables. The
                             *  pre-transformation local variables are thus
                             *  removed from the function definitions   *)
                            currFunc.slocals <- 
                            if((List.length sscompinfo.cfields) = 0) then
                                unaffectedTransVars @ unaffectedLocalVar
                            else
                                [ssvar] @ unaffectedTransVars @ unaffectedLocalVar;

                            let _ = (populate_varLvalMappingTbl (chosenLocalVar @
                            chosenFormalVar) transLvalList) in

                            (*  The guardzone initialization statements that need
                             *  to be attached to the body of the function. We
                             *  will do this attachment in the post processing function
                             *  *)
                            let gz_init_stmts = (
                                    sframeCallStmt @ initGuardCzonesStmts @
                                        initFormalVar)
                            in

                            (*  Note that the below visitAction
                             *  ChangeDoChildrenPost is the key to new types
                             *  being written the file. Otherwise with just
                             *  DoChildren visitAction, the new type was not
                             *  being written to the file.  *)
                             if((List.length sscompinfo.cfields) = 0) then
                             ChangeDoChildrenPost
                             (formalDecl @ localDecl @ [GFun(currFunc, funcLoc)],
                             (self#func_post_processing currFunc gz_init_stmts))
                             else
                             ChangeDoChildrenPost
                             (formalDecl @ localDecl @ [ssvar_gtype] @ [GFun(currFunc, funcLoc)],
                             (self#func_post_processing currFunc gz_init_stmts))
                        end                     
                    end

                     (*  We will skip over all the global elements other than
                     *  variables, variable declarations and functions
                     *)
                    |   _   ->  SkipChildren
                    
                (*  Else condition implies that current global element belongs
                 *  to a file that has not been transformed *)    
                else
                    SkipChildren
                end

        (*===================================================================*)
        (*  The following nopCilVisitor class methods are SPECIFICALLY for
         *  functions ONLY and belong to the previous functionVisitor class.
         *  Thus we must make sure that these must be protected as such.
         *  *)

        (* Method that intercepts all uses of an lval. If it exists in the
         * varReplacementTable then change the reference to struct access of the
         * transformed variable *)
        method vlval (value:lval) : lval visitAction =
            begin
                start_method ();
                log (class_name ++ text ".vlval : ");
                log (text "value:lval : " ++ (dn_lval () value));
                log unalign;

             (* Note that here we are NOT restricting this to be used only in
              * function environment. 
              * The claim is that it should work fine. We need to verify this.
              * *)
             match value with
            (Var(oldVar), offset)when Hashtbl.mem varLvalMappingTbl oldVar ->
                    begin
                        let transLval = Hashtbl.find varLvalMappingTbl oldVar
                        in
                        match transLval with
                        (Var(vinfo),Field(fld,off)) -> begin
                            match fld.ftype with
                            TComp(_,_) ->
                             begin
                              let varField = (getLvalField transLval var_field_name)
                              in
                              ChangeDoChildrenPost( (Var(vinfo), 
                                      Field(fld, Field(varField, offset))), fun x -> x)
                             end
                            | _ -> raise ( Incorrect_Input ("[vlval] Wasn't" ^
                                    " expecting any type for transformed" ^
                                    " variable."))
                        end
                        | _ -> raise (Incorrect_Input ("[globalTransformer:" ^
                                      "lval, expecting structure but got " ^
                                      "something else."))
                    end
            | (Var(oldVar), offset)when Hashtbl.mem varReplacementTable oldVar ->                   
                    begin
                        let transVar = Hashtbl.find varReplacementTable oldVar
                        in

                        (*  Note that the transformedVariable type can be EITHER
                         *  a pointer or a transformed structure.
                         *  The Pointer case happens STRICTLY ONLY FOR global
                         *  variables when their types are ONLY declared and NOT
                         *  defined. In such case, we are forced to use the
                         *  pointer.
                         * *)
                        let transVarType = (Cil.unrollTypeDeep transVar.vtype)
                        in

                        match transVarType with
                        
                        (*  This case happens STRICTLY ONLY FOR global
                         *  variables when their types are ONLY declared and NOT
                         *  defined. In such case, we are forced to use the
                         *  pointer dereference
                         *)

                        |   TPtr(_,_ ) ->
                                    ChangeDoChildrenPost( 
                                        (Mem(Lval(Cil.var transVar)), offset), 
                                        fun x -> x)

                        (*  This is the usual case when type information is
                         *  completely available and transformed variable is the
                         *  transformed structure.
                         * *)
                        |   TComp(_,_) ->
                                begin
                                    let varField = (getVarField transVar var_field_name)
                                    in

                                    ChangeDoChildrenPost( (Var(transVar), 
                                        Field(varField, offset)), fun x -> x)
                                end

                        |   _ -> raise ( Incorrect_Input ("[vlval] Wasn't" ^
                                    " expecting any type for transformed" ^
                                    " variable."))
                    end
                 
            | _ -> DoChildren

            end
           
        (*  Method to intercept the return statement. Before this statement we
         *  will need to call the guardzone uninitialization routines. 
         *  Note that the return statement can itself contain an expression and
         *  hence uninitialization must occur after the evaluation of the
         *  expression  *)

        (*  Another objective of this method is to intercept all memory
         *  allocation functions (and NOT deallocation one's (say free)) and
         *  then set type_size thread-scope variable to value sizeof( *ptr ),
         *  where ptr is the pointer to which the allocation function is
         *  assigning the memory. 
         *  This variable is used in the transformed libc.
         *  *)
        method vstmt (currStmt : stmt ) : stmt visitAction =
            begin
                start_method ();
                log (class_name ++ text ".vStmt : ");
                (*log (text "currStmt:stmt : " ++ (dn_stmt () currStmt)); *)
                log unalign;

                (*  Since this method was initially designed to be a part of the
                 *  functionVisitor class, lets make sure that we are operating
                 *  within a function.
                 * *)
                if (not processing_function) then
                    raise (Incorrect_Input "[transformationVisitor.vlval] vlval called
                    outside a function") ;

            match currStmt.skind with
            |   Return (_ , _) ->
                    let guardzoneProcessing (currStmt : stmt ) =  
                        begin
                            let oldVarList, transVarList = (List.split
                            varMappingList)
                            in
                            let uninitInstrList1 = 
                            (* If the function is to be excluded from the
                             * uninitialization *)
                            if(isFuncExcludedFromInitUninit !funcName
                            !iufunctions_list)
                            then []
                            else
                                List.flatten (List.map
                                    self#func_uninit_guardzone transVarList)
                            in
                            let uninitInstrList = 
                            if((not ((Hashtbl.length varLvalMappingTbl) = 0)) &&
                               (not ((List.length uninitInstrList1) = 0)))
                            then
                              begin
                              let v = (List.nth transVarList 0) in
                              match v with
                              (Var(_),NoOffset) -> raise (Incorrect_Input 
                                "Incorrect type of transformed var")
                              | (Var(ssvar),_) ->
                                let last_field_lval = (Var(ssvar),NoOffset) in
                                let uninit_last_field = 
                                Call(None, Lval((var uninit_rear_guardzone.svar)),
                                [(Lval(last_field_lval))], locUnknown) in
                                (uninitInstrList1 @ [uninit_last_field])
                              | _ -> (uninitInstrList1)
                              end
                            else
                              (uninitInstrList1) in

                            (self#queueInstr uninitInstrList);
                            currStmt
                        end
                    in
                    ChangeDoChildrenPost(currStmt, guardzoneProcessing)

                 (*  Now we will have to scan this instrList to see if there are
                 *  any call to allocation functions followed by set
                 *  instructions. In such a case, the cast used in set
                 *  instruction is the type that we need.
                 *  Note that we need at least two instructions, the call to
                 *  memory allocation function and then the set instruction.
                 *  The above mentioned check of having at least 2 instructions
                 *  is EXTREMELY important because its absence led to a LOT of
                 *  errors.
                 * *)
                |   Instr(instrList) when ((List.length instrList) > 1)->                        
                        let newInstrList = ref [] 
                        in
                        
                        begin
                        for count = 0 to ((List.length instrList) - 2 ) do

                            let currInstr = (List.nth instrList count) 
                            in
                            match currInstr with

                            (*  The basic idea here is that we check the
                             *  name of the function being called to see if
                             *  it belongs to one of the allocations
                             *  functions.
                             *  *)
                            |   Call(Some(temp), Lval((Var(calledFunc), NoOffset)), _ , _ ) 

                                    when (List.mem calledFunc.vname alloc_funcs) ->

                                    (*   Now that we have checked the
                                     *   functions name, we must now ensure
                                     *   that next instruction is a set
                                     *   instruction with the requisite cast *)
                                    begin
                                            
                                        let nextInstr = (List.nth instrList
                                                                (count + 1))
                                        in
                                            
                                        match nextInstr with

                                        (*  Here we check whether the set
                                         *  instruction has a Cast operation
                                         *  being performed on temp variable
                                         *  that malloc assigned to earlier *)
                                        | Set( _ , (CastE(TPtr(reqType, _ ),
                                                    (Lval(temp)) )), _  ) ->
                                          
                                            (*  Now we have confirmed that we
                                             *  have the required type with us,
                                             *  let us set the value of the
                                             *  thread-scope variable, type_size
                                             *  *)
                                            begin
                                                let newInstr =
                                                   Set((Var(type_size), NoOffset),
                                                     SizeOf(reqType), !currentLoc)
                                                in
                                                newInstrList := (List.append !newInstrList 
                                                    [newInstr; currInstr] )

                                            end
                                             
                                        | _ -> newInstrList := (List.append !newInstrList
                                                    [currInstr])

                                    end
                            
                            (*  If the instruction is not of the kind Call then we
                             *  are not bothered    *)
                            | _ -> newInstrList := (List.append !newInstrList [currInstr])

                        done;

                        (*  We must still attach the last instruction. Remember
                         *  that we did not iterate over it.    *)
                        newInstrList := List.append !newInstrList 
                                             [(List.nth instrList
                                                    ( (List.length instrList) - 1))];

                        currStmt.skind <- Instr(!newInstrList);

                        DoChildren
                        end

            | _ -> DoChildren

            end

            (*  We have to over-ride this method because there is
             *  one very specific expression that we would like to replace.
             *  If the expression is of the form &(global_var_decl) where
             *  global_var_decl has type which is only declared and not defined,
             *  we cannot replace it by &( *global_var_ptr).
             *  Hence this kind of expression MUST be replaced with directly
             *  global_var_ptr.
             * *)
            method vexpr (currExpr : exp ) : exp visitAction =
                match currExpr with
                |   AddrOf(currLval)  ->
                        begin
                        match currLval with
                        |   (Var(oldVar), NoOffset)when Hashtbl.mem varReplacementTable oldVar ->                   
                                begin
                                    let transVar = Hashtbl.find varReplacementTable oldVar
                                    in

                                    (*  Note that the transformedVariable type can be EITHER
                                     *  a pointer or a transformed structure.
                                     *  The Pointer case happens STRICTLY ONLY FOR global
                                     *  variables when their types are ONLY declared and NOT
                                     *  defined. In such case, we are forced to use the
                                     *  pointer.
                                    * *)
                                    let transVarType = (Cil.unrollTypeDeep transVar.vtype)
                                    in

                                    match transVarType with
                        
                                    (*  This case happens STRICTLY ONLY FOR global
                                     *  variables when their types are ONLY declared and NOT
                                     *  defined. In such case, we are forced to use the
                                     *  pointer dereference.
                                     *
                                     *  In such a case, we change the current
                                     *  node from &(global_var_decl) to
                                     *  trans_global_var_ptr
                                     *)

                                    |   TPtr(_,_ ) -> 
                                            (*  This happens only in the code
                                             *  section. The references in init
                                             *  section must be handled by
                                             *  initSanitizer object.
                                             * *)
                                            if (processing_function) then
                                                ChangeTo(Lval(Cil.var transVar))
                                            else
                                                (*  Note that this case is the
                                                 *  one for references within
                                                 *  global definitions.
                                                 * *) 
                                            begin
                                                (*  Hence here we need to 
                                                 *  generate a
                                                 *  null void pointer.
                                                 * *)
                                                let null_pointer =
                                                    CastE(Cil.voidPtrType, 
                                                        const_value_0)
                                                in
                                                ChangeTo(null_pointer)
                                            end

                                        (*  Else proceed as you always would.
                                        * *)
                                    |   _ -> DoChildren

                            end

                        |   _ -> DoChildren
                        end

                |   _ -> DoChildren

            (*
             * The goal of this method is to replace memory management 
             * function calls with calls to their wrappers which
             * take guard zone size as argument, if guard zone value
             * can be inferred easily. We look at the return type
             * to which the result of such a function call is casted
             * to determine guard zone size. If result is casted to
             * void* or char* then we do not consider these types
             * to determine guard zone size.
             *)
            method vinst (currInst : instr) : instr list visitAction =

              (* Process single instruction. If it is call to heap memory
               * allocation functions then do the processing as mentioned above.
               * *)
              let processMemMgmtFuncCall (currInst : instr) : instr =
               match currInst with
                Call(retval_opt,Lval(Var(fvinfo),off),expargs,loc) 
                  when (Hashtbl.mem memMgmtFuncsWrappersTbl fvinfo.vname) -> 
                    let newname = Hashtbl.find memMgmtFuncsWrappersTbl fvinfo.vname in

                    (* Unwrap the lval and check if it is syntactically
                     * correct. If not, return false. Returning false
                     * also designates the case when return value is 
                     * not assigned to some variable. *)
                    let unWrapLval (lval_opt : lval option) : lval * bool =
                      match lval_opt with
                        Some(lval) -> (lval,true)
                        (* We don't care what is lval in next case
                         * as we do not use it when return value is false *)
                        | _ -> ((Mem(zero),NoOffset),false)
                    in

                    let isCharOrVoidPtr (t : typ) : bool =
                      if ((t = charPtrType) ||
                          (t = charConstPtrType) ||
                          (t = voidPtrType)) then
                        true
                      else
                        false
                    in

                    (* Checks whether expression represents
                     * constant int. If it does, then returns
                     * integer value of it, otherwise returns 0. *)
                    let isConstInt (e : exp) : int =
                      let int_opt = Cil.isInteger e in
                      match int_opt with
                        Some(i) -> (try (Cil.i64_to_int i) with error -> 0)
                        | None -> 0
                    in

                    (* Compute the request size for given memory 
                     * allocation function call. In case, the request size
                     * cannot be computed statically or there is an error,
                     * then we return 0. If we cannot compute request size
                     * then we will conservatively rely on default malloc,
                     * which will compute guard zone size depending on
                     * actual request size at runtime. *)
                    let computeRequestSize (fname : string) (args : exp list)
                    : int = 
                      if ((String.compare fname "malloc") = 0) then
                        (* In case of malloc, argument 0 represents request size
                         * *)
                        isConstInt (List.nth args 0)
                      else if ((String.compare fname "calloc") = 0) then
                        (* In case of calloc, argument 0 * argument 1 represents
                         * request size *)
                        (isConstInt (List.nth args 0)) *
                        (isConstInt (List.nth args 1))
                      else if ((String.compare fname "realloc") = 0) then
                        isConstInt (List.nth args 1)
                      else if ((String.compare fname "valloc") = 0) then
                        isConstInt (List.nth args 0)
                      else if ((String.compare fname "pvlloc") = 0) then
                        isConstInt (List.nth args 0)
                      else if ((String.compare fname "memalign") = 0) then
                        isConstInt (List.nth args 1)
                      else
                        0
                    in
                        
                    let (retval,present) = unWrapLval retval_opt in

                    (* If return value is assigned to some variable, 
                     * and that variable is a pointer but not char* and void*
                     * and the request size is not 0, then we calculate guard
                     * zone size and use wrappers. *)
                    if (present = true) then
                      let request_size = computeRequestSize fvinfo.vname expargs in
                      let retval_type = Cil.unrollTypeDeep (typeOfLval retval) in

                      if ((isPointerType retval_type) && 
                      (not (isCharOrVoidPtr retval_type)) && 
                      (not (request_size = 0))) then
                        let newvinfo  = Cil.copyVarinfo fvinfo newname in

                        (* Get the type of object pointed by the pointer *)
                        let getPointeeType (pointerType : typ) : typ =
                          match pointerType with
                            TPtr(t,_) -> t
                            | _ -> raise (Incorrect_Input "Unexpected type
                            received")
                        in

                        (* Get the size of element pointed by return val *)
                        let elemsize = sizeOfType (getPointeeType retval_type) in
                        (* Calculate guardzone size *)
                        let gz_size = (getRoundedGZSize elemsize request_size) in
                        let gz_size_exp = Const(CInt64((Int64.of_int gz_size), IUInt,None)) 
                        in
                        let newinstr = Call(retval_opt, Lval(Var(newvinfo),off),
                                      expargs@[gz_size_exp], loc) 
                        in

                        newinstr
                      else
                        currInst
                     else
                        currInst
               
               | _ -> currInst

              in

              let processInstrs (ilist : instr list) : instr list = 
                (List.map processMemMgmtFuncCall ilist)
              in
              
              let newilist = processInstrs [currInst] 
              in
              
              ChangeDoChildrenPost (newilist, processInstrs)

        (*===================================================================*)

        initializer
            begin
            (*  Note that for array definitions and array declarations we will
             *  be assigning the topmost priority while default initialization
             *  will have default priority.
             *
             *  TODO: 
             * *)    
            init_array_defn.svar.vtype <- TFun(voidType, None, false,
            [Attr("constructor",[] ) ] );
                
            init_array_decl.svar.vtype <- TFun(voidType, None, false,
            [Attr("constructor",[] ) ] );
                
            init_ptr_defn.svar.vtype <- TFun(voidType, None, false,
            [Attr("constructor",[] ) ] );
                
            init_default.svar.vtype <- TFun(voidType, None, false,
                [Attr("constructor", [])]);

            f.globals <- f.globals @ [  GFun(init_array_defn, locUnknown);
                                        GFun(init_array_decl, locUnknown);
                                        GFun(init_ptr_defn, locUnknown);
                                        GFun(init_default, locUnknown);
                                     ];
 end
    end

(*  ======================================================================   *)
(* -------------------------------------------------------
 * Some global variables and methods for bounds processing
 * -------------------------------------------------------
 *)
(*
 * NOTE: since we do not use bounds processing, these are commented out. *)

(*
(*
 * This table contains hashmap of functions
 * which are transformed with bound information.
 *)
  let transFuncsTbl = (Hashtbl.create 10)

(*
 * This table contains hashmap of functions which are
 * transformed with safe/unsafe tag.
 *)
  let transSafeFuncsTbl = (Hashtbl.create 10)

  let varinfoHT = (Hashtbl.create 10)
  *)

  (* NOTE: These are support functions related to
   *       bounds tracking which is disabled currently.
   *       Hence disabling these functions also.
   *
  (*
   * Checks if a function name is of a transformed function
   * for bound processing.
   *
   * A function is transformed if it's name ends with "_bnds_trans".
   *)
  let isBndTransFunc (name : string) : bool =
      let tfbs_len = (String.length trans_func_bnd_suffix)
      in
      if((String.length name) <= tfbs_len)
        then false
      else
        ((String.sub name ((String.length name) - tfbs_len) tfbs_len) =
          trans_func_bnd_suffix)

  (*
   * Checks if a function name is of a transformed function
   * for safe/unsafe processing.
   *
   * A function is transformed if it's name ends with "_unsafe".
   *)
  let isUnsafeTransFunc (name : string) : bool =
      let tfbs_len = (String.length trans_func_unsafe_suffix)
      in
      if((String.length name) <= tfbs_len)
        then false
      else
        ((String.sub name ((String.length name) - tfbs_len) tfbs_len) =
          trans_func_unsafe_suffix)

(*
 * Generates a lower bound variable for a given variable.
 * e.g. for a variable "char* p", it's lower bound
 * variable is "p_lo"
 *)
  let genLoBndName (name : string) : string =
        name ^ lo_bnd_suffix 

(*
 * Generate a lower bound variable of type varinfo
 *)
  let genLoBndVInfo (name : string) : varinfo =
    let lbname = (genLoBndName name) 
    in
    if(Hashtbl.mem varinfoHT lbname) then
    begin
        (Hashtbl.find varinfoHT lbname)
    end
    else
        (Cil.makeVarinfo false (lbname) (TInt(IUInt, [])))
        
(*
 * Generates a upper bound variable for a given variable.
 * e.g. for a variable "char* p", it's upper bound
 * variable is "p_hi"
 *)
  let genHiBndName (name : string) : string =
        name ^ hi_bnd_suffix 

(*
 * Generate a upper bound variable of type varinfo
 *)
  let genHiBndVInfo (name : string) : varinfo =
    let hbname = (genHiBndName name) 
    in
    if(Hashtbl.mem varinfoHT hbname) then
        (Hashtbl.find varinfoHT hbname)
    else
        (Cil.makeVarinfo false (hbname) (TInt(IUInt, [])))

  let isLoBndSuffix (name : string) : bool =
    let lbs_len = (String.length lo_bnd_suffix)
    in
    if((String.length name) <= lbs_len)
      then false
    else
      ((String.sub name ((String.length name) - lbs_len) lbs_len) =
      lo_bnd_suffix)


  let isHiBndSuffix (name : string) : bool =
    let lbs_len = (String.length hi_bnd_suffix)
    in
    if((String.length name) <= lbs_len)
      then false
    else
      ((String.sub name ((String.length name) - lbs_len) lbs_len) =
      hi_bnd_suffix)
  
  *)

(*
 * Checks if we need to track bounds of variable specified in
 * varname. We need to track, if variable is a 1D pointer present
 * in ptrVarList. Otherwise, we don't need to track.
 *)
  let is1DPtrVar (lvalue : lval) : bool =
    match lvalue with
    (Var(vinfo), off) -> begin
                         match (Cil.unrollTypeDeep vinfo.vtype) with
                         TPtr(t1, _) -> begin
                                        match t1 with
                                        TPtr(_, _) -> false
                                        | _ -> 
                                          if(vinfo.vname = "stdout") then 
                                            false
                                          else if(vinfo.vname = "stdin") then 
                                            false
                                          else 
                                            true
                          end
                         | _ -> false
                         end
    | _ -> false

  (* check if given pointer is a 1-D pointer *)
  let is1DPtrVarFromTyp (vtype : typ) : bool =
  match (Cil.unrollTypeDeep vtype) with
    TPtr(t1, _) ->  begin
                    match t1 with
                      TPtr(_, _) -> false
                      | _ -> true
                    end
    | _ -> false

  (* Check if given type is a pointer type *)
  let isPtrVarFromTyp (vtype : typ) : bool =
  match (Cil.unrollTypeDeep vtype) with
    TPtr(_, _) -> true
    | _ -> false

  (* 
   * Checks the name of specified variable in the formal param list,
   * if variable is a formal param, returns true.
   * Otherwise false.
   *)
   let rec isFormalParam (vinfo : varinfo) (fpList : varinfo list) : bool =
    match fpList with
    param::params -> if (param.vname = vinfo.vname) 
                     then true
                     else (isFormalParam vinfo params)
    | [] -> false

   let isGlobalParam (vinfo : varinfo) : bool =
       (vinfo.vglob)
   
   let checkNo = ref 0

   let getPrtStmt (file_name : string) : stmt = 
       begin
       (checkNo := (!checkNo + 1););
       (Cil.mkStmt (Instr([(Call(None, Lval(
           (Var(Cil.makeVarinfo false "printf" Cil.voidType)),NoOffset), 
           [Const(CStr("*** " ^ file_name ^ "_" ^ (string_of_int !checkNo) ^
           " ***"))], locUnknown))]))) 
       end


(*  ======================================================================   *)
(*
 * This class finds out the init_guardzones statement for a given function.
 * It then finds out the place where address of guardzoned-variable is taken.
 * It then moves init_guardzones statement to just above that statement.
 *
 * NOTE: This analysis is currently not used.
 *)
(*class initPlacer  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    val mutable rdVarStmtTbl = (Hashtbl.create 10)

    val mutable count = 0

    (*
     * This function takes the list of statements of a function,
     * populates the hash table and returns the modified list of
     * statements with init_guardzones placed in the hashtable
     *)
    method private getInitGuardCzonesStmts (stmts : stmt list) (nstmts : stmt list) : stmt list =
        let getVarinfo (expr : exp) : varinfo = 
            match expr with
            Lval(Var(vinfo),_) -> vinfo
            | _ -> (* We should not arrive to this case*)
                   (Cil.makeVarinfo false "tmp" Cil.voidType)
        in
        let isVarinfoArrayTyp (vinfo: varinfo) : bool =
          let rec isOrigNameArrayTyp (fields : fieldinfo list) : bool =
            match fields with
              f::fs -> if(f.fname = "orig_var") then
                        match f.ftype with
                        TArray(_,_,_) -> true
                        | _ -> false
                       else
                        (isOrigNameArrayTyp fs)
              | [] -> false
          in
          let t = (Cil.unrollTypeDeep vinfo.vtype) in
          match t with
          TComp(cinfo,_) -> (isOrigNameArrayTyp cinfo.cfields)
          | _ -> false
        in
        let rec getInitGuardCzonesInstr (ilist: instr list) (nilist : instr list) : stmt = 
            match ilist with
            i::is -> begin
                match i with
                Call(_,Lval(Var(fname), off),exprs,_) ->
                if(fname.vname = "init_guardzones") then
                begin
                    (*let vinfo = (getVarinfo (List.hd exprs)) in
                    if(not (isVarinfoArrayTyp(vinfo))) then
                      begin
                        (Hashtbl.add rdVarStmtTbl vinfo.vname i);
                        (getInitGuardCzonesInstr is (nilist))
                      end
                    else
                      (getInitGuardCzonesInstr is (nilist@[i])) *)
                    (count <- count + 1);
                    (getInitGuardCzonesInstr is (nilist@[i]))
                end
                else
                  (getInitGuardCzonesInstr is (nilist@[i]))
                | _ -> (getInitGuardCzonesInstr is (nilist@[i]))
            end
            | [] -> (Cil.mkStmt (Instr(nilist))) 
        in
        match stmts with
        s::sl -> begin
            match s.skind with
            Instr(ilist) -> (self#getInitGuardCzonesStmts sl (nstmts@[(getInitGuardCzonesInstr
            ilist [])]))
            | Block(blk) -> 
                    let nbstmts = (self#getInitGuardCzonesStmts blk.bstmts []) in
                    (self#getInitGuardCzonesStmts sl (nstmts@nbstmts))
            | _ -> (self#getInitGuardCzonesStmts sl (nstmts@[s]))
        end
        | [] -> nstmts

    method private getGZVarInitInstr (vinfo : varinfo) : stmt * bool =
        if((Hashtbl.mem rdVarStmtTbl vinfo.vname) = true) then
            (Cil.mkStmtOneInstr (Hashtbl.find rdVarStmtTbl vinfo.vname)), true
        else
            Cil.dummyStmt, false

    method private addInitIfExpGZVarAddr (elist : exp list) (slist : stmt list)
    : stmt list =
      let rec processOffset (off : offset) (slist1 : stmt list) :  stmt list =
          match off with
          NoOffset -> slist1
          | Field(_,off1) -> (processOffset off1 slist1)
          | Index(e1,off1) -> 
              let rslist = (self#addInitIfExpGZVarAddr [e1] []) in
                (processOffset off1 (slist1@rslist))
      in
      match elist with
        e::es -> begin
          match e with
            Lval(Var(_),off) -> 
                let s1 = (processOffset off []) in
                (self#addInitIfExpGZVarAddr es (slist@s1))
            | Lval(Mem(e1),off) ->
                let s1 = (self#addInitIfExpGZVarAddr [e1] []) in
                let s2 = (processOffset off []) in
                (self#addInitIfExpGZVarAddr es (slist@s1@s2))
            | AddrOf(Var(vinfo),off) -> 
                let s1,bret = (self#getGZVarInitInstr vinfo) in
                let s2 = (processOffset off []) in
                if(bret = true) then
                  (self#addInitIfExpGZVarAddr es (slist@[s1]@s2))
                else
                  (self#addInitIfExpGZVarAddr es (slist@[]@s2))
            | AddrOf(Mem(e1),off) ->
                let s1 = (self#addInitIfExpGZVarAddr [e1] []) in
                let s2 = (processOffset off []) in
                (self#addInitIfExpGZVarAddr es (slist@s1@s2))
            | StartOf(Var(vinfo),off) ->
                let s1,bret = (self#getGZVarInitInstr vinfo) in
                let s2 = (processOffset off []) in
                if(bret = true) then
                  (self#addInitIfExpGZVarAddr es (slist@[s1]@s2))
                else
                  (self#addInitIfExpGZVarAddr es (slist@[]@s2))
            | StartOf(Mem(e1),off) ->
                let s1 = (self#addInitIfExpGZVarAddr [e1] []) in
                let s2 = (processOffset off []) in
                (self#addInitIfExpGZVarAddr es (slist@s1@s2))
            | _ -> (self#addInitIfExpGZVarAddr es slist)
        end
        | [] -> slist

    method private addInitBeforeGZVarAddrInstr (ilist : instr list) (nslist :
        stmt list) : stmt list =
      match ilist with
      i::is -> begin
          match i with
          Set(l,e,_) -> 
              let ll = (self#addInitIfExpGZVarAddr [Lval(l)] []) in
              let sl = (self#addInitIfExpGZVarAddr [e] []) in
              (self#addInitBeforeGZVarAddrInstr is (nslist@ll@sl))
          | Call(lo,e1,el,_) -> begin
              match lo with
                Some(l) ->
                  let ll = (self#addInitIfExpGZVarAddr [Lval(l)] []) in
                  let sl = (self#addInitIfExpGZVarAddr ([e1]@el) []) in
                  (self#addInitBeforeGZVarAddrInstr is (nslist@ll@sl))
                | _ -> 
                  let sl = (self#addInitIfExpGZVarAddr ([e1]@el) []) in
                  (self#addInitBeforeGZVarAddrInstr is (nslist@sl))
          end
          | _ -> (self#addInitBeforeGZVarAddrInstr is (nslist))
      end
      | [] -> nslist

    method private addInitBeforeGZVarAddrStmt (nstmts : stmt list) (nistmts :
        stmt list) : stmt list =
      match nstmts with
      stm::stmts -> begin
          match stm.skind with
          Instr(ilist) -> 
              let nslist = (self#addInitBeforeGZVarAddrInstr ilist []) in
              begin
                if(not ((List.length nslist) = 0)) then
                 begin
                  ((List.hd nslist).labels <- stm.labels);
                  (stm.labels <- []);
                 end;

                (self#addInitBeforeGZVarAddrStmt stmts (nistmts@nslist@[stm]))
              end
          | Return(Some(e),_) ->
              let nslist = (self#addInitIfExpGZVarAddr [e] []) in
              begin
                if(not ((List.length nslist) = 0)) then
                begin
                  ((List.hd nslist).labels <- stm.labels);
                  (stm.labels <- []);
                end;

                (self#addInitBeforeGZVarAddrStmt stmts (nistmts@nslist@[stm]))
              end
          | If(e,iblk,eblk,_) ->
              let nslist = (self#addInitIfExpGZVarAddr [e] []) in
              let niblist = (self#addInitBeforeGZVarAddrStmt iblk.bstmts []) in
              let neblist = (self#addInitBeforeGZVarAddrStmt eblk.bstmts []) in
              let istmt = If(e,(Cil.mkBlock niblist),(Cil.mkBlock neblist),locUnknown) in
              begin
                if(not ((List.length nslist) = 0)) then
                begin
                  ((List.hd nslist).labels <- stm.labels);
                  (stm.labels <- []);
                end;

                (stm.skind <- istmt);

                (self#addInitBeforeGZVarAddrStmt stmts 
                (nistmts@nslist@[stm]))
              end
          | Switch(e,blk,sl,_) ->
              let nslist = (self#addInitIfExpGZVarAddr [e] []) in
              let nblist = (self#addInitBeforeGZVarAddrStmt blk.bstmts []) in
              let nslist1 = (self#addInitBeforeGZVarAddrStmt sl []) in
              let sstmt = Switch(e,(Cil.mkBlock nblist),nslist1,locUnknown) in
              begin
                if(not ((List.length nslist) = 0)) then
                begin
                  ((List.hd nslist).labels <- stm.labels);
                  (stm.labels <- []);
                end;
                
                (stm.skind <- sstmt);
                
                (self#addInitBeforeGZVarAddrStmt stmts 
                (nistmts@nslist@[stm]))
              end
          | Loop(blk,_,so1,so2) ->
              let nblist = (self#addInitBeforeGZVarAddrStmt blk.bstmts []) in
              let lstmt = Loop((Cil.mkBlock nblist),locUnknown,so1,so2) in
              begin
                (stm.skind <- lstmt);
                (self#addInitBeforeGZVarAddrStmt stmts (nistmts@[stm]));
              end
          | Block(blk) ->
              let nblist = (self#addInitBeforeGZVarAddrStmt blk.bstmts []) in
              let bstmt = Block(Cil.mkBlock nblist) in
              begin
                (stm.skind <- bstmt);
                (self#addInitBeforeGZVarAddrStmt stmts (nistmts@[stm]));
              end
          | TryFinally(blk1,blk2,_) ->
              let nblist1 = (self#addInitBeforeGZVarAddrStmt blk1.bstmts []) in
              let nblist2 = (self#addInitBeforeGZVarAddrStmt blk2.bstmts []) in
              let tfstmt = TryFinally((Cil.mkBlock nblist1),(Cil.mkBlock
              nblist2),locUnknown) in
              begin
                (stm.skind <- tfstmt);
                (self#addInitBeforeGZVarAddrStmt stmts (nistmts@[stm]));
              end
          | TryExcept(blk1,(ilist,e),blk2,_) ->
              let nblist1 = (self#addInitBeforeGZVarAddrStmt blk1.bstmts []) in
              let nilist = (self#addInitBeforeGZVarAddrInstr ilist []) in
              let nslist = (self#addInitIfExpGZVarAddr [e] []) in
              let nblist2 = (self#addInitBeforeGZVarAddrStmt blk2.bstmts []) in
              let testmt = TryExcept((Cil.mkBlock nblist1),
                (ilist,e),(Cil.mkBlock nblist2),locUnknown) in       
              begin
                if(not ((List.length nilist) = 0)) then
                begin
                  ((List.hd nilist).labels <- stm.labels);
                  (stm.labels <- []);
                end
                else if(not ((List.length nslist) = 0)) then
                begin
                  ((List.hd nslist).labels <- stm.labels);
                  (stm.labels <- []);
                end;
                
                (stm.skind <- testmt);

                (self#addInitBeforeGZVarAddrStmt stmts 
                (nistmts@nilist@nslist@[stm]))
              end
          | _ -> (self#addInitBeforeGZVarAddrStmt stmts (nistmts@[stm]))
      end
      | [] -> nistmts

      
    (*
     * Algorithm:
     * 1. Create a hashtable of guardzone variable name and it's init statement
     *    by traversing the function body.
     * 2. Again traverse a function body, this time with the aim of finding out
     *    the place where the address of guardzoned-variable is taken.
     *    
     *    Once we find such a place, insert initialization statement before that
     *    statement and remove the entry from the hash table.
     * 3. Repeat step 2 until hash table is empty. We can empty the hash table
     *    in one scan of the body of the function.
     *)
    method private processInitializationCalls (func : fundec) : fundec * bool =
        let nstmts = (self#getInitGuardCzonesStmts func.sbody.bstmts []) in
        (*let nistmts = (self#addInitBeforeGZVarAddrStmt nstmts []) in*)
        begin
            (*(func.sbody.bstmts <- nstmts);*)
            let str = (" \n\n**** Count for " ^ (func.svar.vname) ^ " : ") in
            begin
            (print_string str);
            (print_string (string_of_int count));
            (print_string "\n\n");
            (count <- 0);
            (func, true)
            end
        end

    method vglob (currGlob : global) : global list visitAction =
         if ((permitInstrumentation currGlob) &&
             (permitTransformation currGlob)) then
             match currGlob with
             GFun(func, _) -> begin
                    if (skipFunction func.svar.vname file_name) then
                        SkipChildren
                    else 
                    begin
                        (Hashtbl.clear rdVarStmtTbl);
                        let tfunc, bret = (self#processInitializationCalls func)
                        in
                        (*in
                        if(bret = true) then
                            (ChangeTo [GFun(tfunc, locUnknown)])*)
                        SkipChildren
                        (*else
                            SkipChildren*)
                    end
                    end
             | _ -> SkipChildren
         else
             SkipChildren

    end*)

(*  ======================================================================   *)

(*
 * This class creates 2 copies of the function body.
 * For the first copy, we modify it's name by appending
 * "_unsafe" to it. To the second copy, we don't do anything.
 *
 * The idea is functions with "_unsafe" to them are the functions
 * which accept unsafe pointer in the input and hence we need to
 * keep guardzone check inside such a function.
 *
 * NOTE: The analysis provided by this option is currently not used.
 *)
(*class transformFunctionsSafeUnsafe  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    (* This method creates a list of types from list of formal params *)
    method private getTypListV (formals : varinfo list) (tlist : typ list) :
        typ list =
      match formals with
      f::fs -> (self#getTypListV fs (tlist@[f.vtype]))
      | _ -> tlist

    (* This method creates a list of types from list of 
     * (string * typ * attributes) list
     *)
    method private getTypListL (formals : (string * typ * attributes) list) 
    (tlist : typ list) : typ list =
      match formals with
      (_,vtype,_)::fs -> (self#getTypListL fs (tlist@[vtype]))
      | _ -> tlist

    (* check if at least one formal parameter is pointer *)
    method private isAtleastOneParamPtr (typ_formals : typ list) : bool = 
        match typ_formals with
        f::fs -> if (isPtrVarFromTyp f) then
                    true
                 else
                    (self#isAtleastOneParamPtr fs)
        | [] -> false

    (*
     * Lets use vglob method of nopCilVisitor to track function
     * declarations and definitions.
     *
     * For every function, we create 2 copies. One copy has 
     * original name and other copy has "_unsafe" appended.
     *)
    method vglob (currGlob : global) : global list visitAction =
         if ((permitInstrumentation currGlob) &&
             (permitTransformation currGlob)) then
             match currGlob with
            GVarDecl
            (vinfo,_) -> begin 
                         match vinfo.vtype with
                         TFun(_,args,_,_) -> 
                          if((skipFunction vinfo.vname file_name) || 
                            (vinfo.vname = "main")) then
                            SkipChildren
                          else
                          begin
                            (* We make a copy of the function, if it has at least
                             * one formal parameter of pointer type. *)
                            let typlist = 
                                (self#getTypListL (Cil.argsToList args) []) in
                            if(self#isAtleastOneParamPtr typlist) then
                            let tvinfo = (Cil.copyVarinfo vinfo vinfo.vname) in
                              begin
                                (*
                                 * Add this function to safeFunction table.
                                 * We use this table later-on to find out which 
                                 * functions are transformed.
                                 *)
                                (Hashtbl.add transSafeFuncsTbl vinfo.vname
                                typlist);
                                tvinfo.vname <- (tvinfo.vname ^ trans_func_unsafe_suffix);
                                ChangeTo([currGlob] @ [GVarDecl(tvinfo,locUnknown)]);
                              end
                            else
                                SkipChildren
                          end
                         | _ -> SkipChildren
            end
            | GFun(func, _) -> begin
               (*
                * Don't transform function if it is one of the
                * constructor/destructor function or main.
                *)
                if((skipFunction func.svar.vname file_name) || 
                  (func.svar.vname = "main")) then
                  SkipChildren
                else  
                 (* We make a copy of the function, if it has at least
                  * one formal parameter of pointer type. *)
                 let typlist = (self#getTypListV func.sformals []) in
                 if(self#isAtleastOneParamPtr typlist) then
                  begin
                      (Hashtbl.add transSafeFuncsTbl func.svar.vname
                      typlist);
                      (* make a copy of function otherwise CIL will modify
                       * original copy. *)
                      let tfunc = (Cil.copyFunction func func.svar.vname) in
                        begin
                          (* append "_unsafe" to function name in new copy. *)
                          tfunc.svar.vname <- (tfunc.svar.vname ^ trans_func_unsafe_suffix);
                          ChangeTo([currGlob] @ [GFun(tfunc,locUnknown)]);
                        end
                  end
                 else
                   SkipChildren
            end
            | _ -> SkipChildren
         else
            SkipChildren
  end *)

(*  ======================================================================   *)
(*
 * Variables to keep track of removed/kept checks 
 *)
let total_checks = ref 0

let removed_checks = ref 0

let kept_checks = ref 0

(* This class processes the file annotations generated by CCured.
 * For every is_char_guard check present in the file, it checks if
 * the pointer dereferenced in the check is safe or unsafe.
 * If safe, it removes the is_char_guard check, otherwise
 * it keeps the is_char_guard check.
 *)
class remSafeIsCharGuardCVisitor  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    (*
     * This method checks if given expression represents
     * double pointer dereference such as *(p->q) as it
     * will be represented as *(( *p).q).
     *)
    method private isExprDDereferenced (expr : exp) : bool =
        match expr with
        Lval(Mem(Lval(Mem(_),_)),_) -> true
        | _ -> false

    method private isSafePtr (vtype : typ) : bool =
        match vtype with
        (* If it is a pointer, then check if it is SAFE. *)
        TPtr(_, attrs) -> begin
            (* Now we need to get the last type attribute corresponding to
             * _ptrnode for this pointer and check if it is SAFE.
             *
             * We check the last type attribute, because, at a time
             * we can have only 1 dereference. So for a double pointer
             * such as int *1 *2 p; and expression such as *p,
             * we need to check if *2 is SAFE or not. Hence we check
             * type attributes in reverse.
             * 
             * This function expects a reversed attribute list.
             *)
            let rec isLastPtrNodeHasSafeTypeAttr (attrs : attribute list) : bool =
              match attrs with
              Attr(str, aparamlist)::ats -> begin
                  if(str = "_ptrnode") then
                    let aparam = (List.hd (List.rev aparamlist)) in
                    match aparam with
                    AInt(nodeid) -> 
                            (* 
                             * idNode is mapping from ids to nodes generated by
                             * CCured type analysis algorithm.
                             * We access that hashtable here and find out the
                             * type of the pointer corresponding to the node id.
                             *)
                            let pnode : Ptrnode.node = (Hashtbl.find Ptrnode.idNode nodeid) in
                            if(pnode.Ptrnode.kind = Ptrnode.Safe) then
                            begin
                              print_CCured_node_kind pnode;
                              true
                            end
                            else
                            begin
                              print_CCured_node_kind pnode;
                              false
                            end;
                    | _ -> (* I don't expect that this case will occur.
                            * If it does, then it means that there is 
                            * an attribute like _ptrnode(Something besides Int)
                            * which is not what is expected as per CCured
                            *)
                            (isLastPtrNodeHasSafeTypeAttr ats)
                  else
                    (isLastPtrNodeHasSafeTypeAttr ats)
              end                     
              | [] -> 
                     (* 
                     * we didnt find any __ptrnode__, so better be conservative
                     * and return false 
                     *)
                     false
            in  
            (isLastPtrNodeHasSafeTypeAttr (List.rev attrs))
        end
        (* If it is not a pointer, then it is obviously SAFE. *)
        | _ -> true

    (*
     * Given an expression used as a first parameter to
     * is_char_guard, this function checks if the pointers
     * involved in the expression are safe. If they are safe,
     * then it returns true, otherwise false.
     *)
    method private isSafeExpr (expr : exp) (isExprDeref : bool) : bool =
      match expr with
      Lval(Var(vinfo), NoOffset) ->
          (* we don't care about field offset here, because
           * if object corresponding to vinfo is SAFE, then field
           * offset inside object is SAFE.
           *)
          (* we need to check if vinfo is SAFE pointer, if it
           * is dereferenced. E.g., in case of ( *p ), where vinfo is p.
           *)
          if (isExprDeref = true) then
            (self#isSafePtr vinfo.vtype)
          else
            (* if expr is not dereferenced, then it is SAFE. *)
            true

      (* This represents the case of an array and structure indexing.
       * Arrays are SEQ pointers in CCured, so we do not need
       * any more checks to determine if the expression is SAFE or not
       *)
      | Lval(Var(vinfo), Field(_,_)) 
      | Lval(Var(vinfo), Index(_,_)) -> false

      (* 
       * The expr below matches expressions such as
       * *p, *(p->q), *(p->q->r), *(p->q).r etc.
       *
       * So for *(p->q), we need to check that p is SAFE
       * and q is also SAFE.
       *)
      | Lval(Mem(expr1), off) -> 
              (* we care about offset because we need to
               * check that q is SAFE. *)
              let sret = (self#isSafeExpr expr1 true) in
              if (sret = true) then
              begin
              (* W.r.t above example, if sret = true then
               * it means that p is SAFE. Now we need to 
               * ensure that q is SAFE, only if q is dereferenced.
               * Case of *(p->q). If we have *(p).q, then we don't need
               * to check if q is SAFE as it is not dereferenced.
               *)
                let rec isOffsetSafe (off : offset) : bool =
                  match off with
                  (* case of *p. since p is SAFE, *p is SAFE *)
                  NoOffset -> true
                  | Field(finfo, off1) -> ((self#isSafePtr finfo.ftype) &
                  (isOffsetSafe off1))
                  | Index(expr1, off1) -> ((self#isSafeExpr expr1
                  (self#isExprDDereferenced expr1)) & (isOffsetSafe off1))
                in
                if(isExprDeref = true) then
                  (isOffsetSafe off)
                else
                  true
              end
              else false
      (* For cast, we see if pointer is marked as SAFE by CCured *)
      | CastE(_, expr1) -> 
              if (isExprDeref = true) then
                (self#isSafeExpr expr1 isExprDeref)
              else
                 false
      | AddrOf(lvalue) -> 
              if (isExprDeref = true) then
                (self#isSafeExpr (Lval(lvalue)) isExprDeref)
              else
                 false
      | StartOf(lvalue) ->
              if (isExprDeref = true) then
                (self#isSafeExpr (Lval(lvalue)) isExprDeref)
              else
                 false
      | _ -> false

    (*
     * we check if actual arguments are safe
     * or unsafe pointers using CCured typing rules.
     *)
    (*method private areCompatibleParams (t : typ) (expr : exp) : bool =
      (* is this an expression for 0? *)
      let isZero (expr : exp) : bool = 
          match expr with
          Const(CInt64(i,_,_)) ->
            if((i64_to_int i) = 0)
            then true
            else false
          | _ -> false
      in
      (* lets check if the expression involves any UNSAFE pointer.
       * If it is, then we obviously need to use UNSAFE version of a 
       * function, otherwise we use SAFE version.
       *)
      if(not (self#isSafeExpr expr true)) then
          false
      else
      begin
          (* The expression is SAFE, now check if it's type
           * is compatible with type of formal argument of a
           * function.
           *)
          (* if expr is not a subtype of type t and
           * expr is not zero, then these are not compatible
           * parameters.
           *
           * We allow assignment of 0 to pointer.
           *)
           if((not (! Ptrnode.isSubtype (Cil.typeOf expr) t)) &&
              (not (isZero expr))) then
                false
           else
           match expr with
           (* if this is a nested cast, then go down *)
            CastE(t1,expr1) -> (self#areCompatibleParams t1 expr1)
            | _ -> true
      end *)

    (*
     * This function checks if the given function call has used
     * all actual parameters safely. 
     *
     * In order to check this, we check if actual arguments are safe
     * or unsafe pointers using CCured typing rules.
     *)
    (*method private isSafeCall (fargs : typ list)(exprs : exp list) : bool =
      match (fargs,exprs) with
      (f::fs, e::es) -> if(isPtrVarFromTyp f) then
                          if(self#areCompatibleParams f e) then
                            (self#isSafeCall fs es)
                          else
                            false
                        else
                          (self#isSafeCall fs es)
      (* everything is fine, return true *)
      | ([], []) -> true
      (* we should not arrive at this case : be safe, return false *)
      | (_, _) -> false *)
 
    (*
     * Scan instructions, and look for is_char_red calls.
     * Check if these calls can be eliminated by using CCured analysis
     *)
    method vinst (currInst : instr) : instr list visitAction =
        match currInst with
        Call(ret,Lval(Var(fname), off),exprs,loc) -> begin
            if(fname.vname = "is_char_guard") then
                begin
                (* check if this check can be removed *)
                (total_checks := !total_checks + 1);
                let _ = (Cil.dn_instr () currInst) in
                let fexpr = (List.hd exprs) in
                if((self#isSafeExpr fexpr (self#isExprDDereferenced fexpr)) = true) then
                    begin
                        (removed_checks := !removed_checks + 1);
                        let _ = (Cil.dn_instr () currInst) in
                    ChangeTo []
                    end
                else
                    begin
                        (kept_checks := !kept_checks + 1);
                    SkipChildren
                    end
                end
            (*else if(Hashtbl.mem transSafeFuncsTbl fname.vname) then
              begin
              (* if this is the function which is present in
               * transSafeFuncsTbl, then we process this call.
               *)
                let fargs = (Hashtbl.find transSafeFuncsTbl fname.vname) in
                (* check if the actual arguments are SAFE.
                 * If all actual arguments which are pointers are safe,
                 * then this call is SAFE. If call is SAFE, then we don't
                 * need to do anything with it. If call is not SAFE, then we
                 * use unsafe version of it.
                 *)
                if(not (self#isSafeCall fargs exprs)) then
                  let tfname = (Cil.copyVarinfo fname fname.vname) in
                    begin
                      tfname.vname <- (tfname.vname ^ trans_func_unsafe_suffix);
                      ChangeTo[(Call(ret,Lval(Var(tfname),off),exprs,loc))];
                    end
                else
                  SkipChildren
              end*)
            else
                SkipChildren
        end
        | _ -> SkipChildren

    (*  
     *  The objective of the current method is to filter out the functions
     *  that will be then analyzed.
     *)
     method vglob (currGlob : global) : global list visitAction =
         (* 
          * If the function is allowed to be instrumented,
          * then we go ahead and instrument it.
          * otherwise we skip it's instrumentation.
          *
          * We are eliminating guard zone checks from the functions only,
          * so we filter out non-function Globals.
          *)
         if (permitInstrumentation currGlob) then
             match currGlob with
            | GFun(func, _) -> begin
                    if(skipFunction func.svar.vname file_name) then
                        SkipChildren
                    else DoChildren
                    end
            | _ -> SkipChildren
         else
            SkipChildren

    end 

(*  ======================================================================   *)
(* This class replaces the memory allocation functions to original untransformed
 * functions in glibc if the pointer that points to the allocated region is 
 * SAFE.
 *)
class replaceMemallocToOrigForSafePtr  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    method vinst (currInst : instr) : instr list visitAction =
        match currInst with
        Call(lval_opt,Lval(Var(fvinfo),off),expargs,loc) 
          when (Hashtbl.mem memMgmtFuncsPtrParamTbl fvinfo.vname) -> 
              let argnolist,newname = Hashtbl.find memMgmtFuncsPtrParamTbl fvinfo.vname in

              let expr_to_check (argno : int) : exp = 
                if(argno = 0) then
                  match lval_opt with
                    Some(lval) -> Lval(lval)
                    | _ -> raise (Incorrect_Input ("The return value of " ^
                              fvinfo.vname ^ " should be assigned to some variable"))
                else
                    List.nth expargs (argno - 1)
              in

              (* Check if all required arguments of a function call
               * are SAFE. *)
              let rec are_all_args_safe (args : int list) : bool =
                let is_arg_safe (arg : int) : bool =
                    try (isSafeExp (expr_to_check arg)) 
                    with error -> false
                in
                  List.for_all is_arg_safe args
              in

              if(are_all_args_safe argnolist) then
                  let newvinfo  = copyVarinfo fvinfo newname in
                  let newinstr = Call(lval_opt,Lval(Var(newvinfo),off),expargs,loc) in
                  ChangeTo [newinstr] 
              else
               SkipChildren
        | _ -> SkipChildren

    method vglob (currGlob : global) : global list visitAction =
         (* 
          * If the function is allowed to be instrumented,
          * then we go ahead and instrument it.
          * otherwise we skip it's instrumentation.
          *
          * We are replacing memory allocation functions to,
          * original functions only for safe pointers.
          *)
         if (permitInstrumentation currGlob) then
             match currGlob with
            | GFun(func, _) -> begin
                    if(skipFunction func.svar.vname file_name) then
                        SkipChildren
                    else DoChildren
                    end
            | _ -> SkipChildren
         else
            SkipChildren

    end 

(*  ======================================================================   *)

(*
 * NOTE: This analysis is not used currently.
 *)
(*class transformFunctions  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    val mutable cnt = ref 0
 
    (*
     * This method checks if at least one parameter is a pointer.
     * If yes, then returns true; otherwise false.
     * We don't transform functions that don't have any pointer as a formal
     * parameter.
     *)
    method private transformFormalParams (fpList : varinfo list) (tfpList :
        varinfo list) : varinfo list =
    match fpList with
    fp::fps -> if(is1DPtrVar(Var(fp),NoOffset)) 
               then (self#transformFormalParams fps
               (tfpList@[fp]@[genLoBndVInfo fp.vname]@[genHiBndVInfo fp.vname]))
               else (self#transformFormalParams fps (tfpList@[fp]))
    | [] -> (tfpList)

    method private transformFormalParamsString (fpList : (string * typ *
    attributes) list) (tfpList : (string * typ * attributes) list) : (string *
    typ * attributes) list =
    match fpList with
    (str,vtype,vattr)::fps -> if(is1DPtrVarFromTyp(vtype)) 
               then if (not (str = ""))
                    then
                      (self#transformFormalParamsString fps
                      (tfpList@[(str,vtype,vattr)]@[((genLoBndName
                      str),Cil.uintType,vattr)]@[((genHiBndName
                      str),Cil.uintType,vattr)]))
                    else 
                      begin
                        cnt := !cnt + 1;
                      (self#transformFormalParamsString fps
                      (tfpList@[(str,vtype,vattr)]@[((genLoBndName
                      ("tmp" ^ (string_of_int !cnt))),Cil.uintType,vattr)]@[((genHiBndName
                      ("tmp" ^ (string_of_int !cnt))),Cil.uintType,vattr)]))
                      end
               else (self#transformFormalParamsString fps (tfpList@[(str,vtype,vattr)]))
    | [] -> (tfpList)

    method vglob (currGlob : global) : global list visitAction =
         if (permitInstrumentation currGlob) then
             match currGlob with
            GVarDecl(vinfo,_) -> begin 
                                match vinfo.vtype with
                                TFun(rtype,args,vararg,attr) -> 
                                    if((skipFunction vinfo.vname file_name) || 
                                       (vinfo.vname = "main") ||
                                       ((vinfo.vinline = false) && 
                                       (not (vinfo.vstorage = Static)))) then
                                      SkipChildren
                                    else
                                      begin
                                          let arglist = (Cil.argsToList args) in
                                          let tfpList = (self#transformFormalParamsString
                                          arglist []) in
                                          begin
                                            let tvinfo = (Cil.copyVarinfo vinfo
                                            vinfo.vname) in
                                            begin
                                              tvinfo.vname <- (tvinfo.vname ^
                                                        trans_func_bnd_suffix);
                                              tvinfo.vtype <-
                                                  TFun(rtype,Some(tfpList),vararg,attr);
                                              ChangeTo([currGlob] @
                                              [GVarDecl(tvinfo,locUnknown)]);
                                            end
                                          end
                                       end
                                | _ -> SkipChildren
                                end
            | GFun(func, _) -> begin
                    (*
                     * Don't transform function if it is one of the
                     * constructor/destructor function or main or
                     * not a static/inline function.
                     *)
                    if((skipFunction func.svar.vname file_name) || 
                       (func.svar.vname = "main") ||
                       ((func.svar.vinline = false) && 
                        (not (func.svar.vstorage = Static)))) then
                        SkipChildren
                    else  
                      begin
                        cnt := 0;
                        let tfpList = (self#transformFormalParams
                        func.sformals []) in
                        begin
                            (Hashtbl.add transFuncsTbl func.svar.vname
                            func.sformals);
                            let tfunc = (Cil.copyFunction func func.svar.vname) in
                            begin
                            tfunc.svar.vname <- (tfunc.svar.vname ^
                            trans_func_bnd_suffix);
                            tfunc.sformals <- tfpList;
                            ChangeTo([currGlob] @ [GFun(tfunc,locUnknown)]);
                            end
                        end
                      end
                    end
            | _ -> SkipChildren
         else
            SkipChildren
  end *)

(*  ======================================================================   *)

(* 
 * For conservative mode analysis, we tag all the formal pointer
 * arguments of a function and global pointers as WILD.
 *
 * This mode is to be used for separate compilation only.
*)
class wildTagFormalGlobalPointerVisitor (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    method private addWildAttrToType (t:typ) : typ * bool =
      match t with
        TPtr(t,attrs) -> 
           (TPtr(t,(Cil.addAttribute (Attr("wild",[])) attrs)),true)
        | _ -> (t,false)

    (* This method checks if the given vinfo is of pointer type,
     * and if it is, it will add wild attribute to it and return true,
     * if it is not a pointer type, then it will return original varinfo,
     * and return false.
     *)
    method private processVinfo (vinfo : varinfo) : (varinfo * bool) =
      match vinfo.vtype with
        TPtr(t,attrs) -> 
          begin
            let t',ret = self#addWildAttrToType vinfo.vtype in
            begin
            if(ret) then
                vinfo.vtype <- t';
            (vinfo,ret)
            end
          end
        | TFun(ftyp,sl,op,b) -> 
          begin
            let t',ret = self#addWildAttrToType ftyp in
            begin
            if(ret) then
                vinfo.vtype <- TFun(t',sl,op,b);
            (vinfo,ret)
            end
          end
        | _ -> (vinfo,false)

   (*
    * For a function definition, get it's formals, and add wild
    * attribute to all of them from it having pointer type.
    *)
   method vfunc (currFunc : fundec) : fundec visitAction = 

      let rec processFormals (sfs:varinfo list) (sfs':varinfo list)
      (atleastOneChanged:bool) : (varinfo list * bool) =
          match sfs with
          [] -> (sfs',atleastOneChanged)
         | f::fs -> 
            let f',isVinfochanged = self#processVinfo f in
              if(isVinfochanged) then
                  processFormals fs (sfs'@[f']) true
              else
                  processFormals fs (sfs'@[f]) atleastOneChanged
      in

      let sformals',ret = processFormals currFunc.sformals [] false in
      let fvinfo',ret' = self#processVinfo currFunc.svar in
      if (ret || ret') then
        begin
          if(ret) then
            currFunc.sformals <- sformals';
          if(ret') then
            currFunc.svar <- fvinfo';
          ChangeTo currFunc
        end
      else
        SkipChildren

    (*  
     *  The objective of the current method is to filter out the functions
     *  that will be then instrumented.
     *)
     method vglob (currGlob : global) : global list visitAction =
         (* 
          * If the function is allowed to be instrumented,
          * then we go ahead and instrument it.
          * otherwise we skip it's instrumentation.
          *
          * We are introducing bounds for pointers local to a function,
          * so we filter out non-function Globals.
          *)
         if ((permitInstrumentation currGlob) && (permitTransformation currGlob)) then
             match currGlob with
            | GFun(func, _) ->
                    if((skipFunction func.svar.vname file_name)) then
                        SkipChildren
                    else DoChildren
            | GVarDecl(vinfo,loc) ->
                let vinfo',ret' = self#processVinfo vinfo in
                if(ret') then
                    ChangeTo [GVarDecl(vinfo',loc)]
                else
                  SkipChildren
            | GVar(vinfo,init,loc) ->
                let vinfo',ret' = self#processVinfo vinfo in
                if(ret') then
                    ChangeTo [GVar(vinfo',init,loc)]
                else
                  SkipChildren
            | _ -> SkipChildren
         else
            SkipChildren
    end
    
(*  ======================================================================   *)
  
(*
 * NOTE: This analysis is not used currently.
 *)
(*  The objective of an object of this class is to introduce bound variables
 *  for all pointers local to a function.
 *  This class constitutes the third "sweep"/"run" of the target file after both
 *  the global variables and the local variables have been transformed and
 *  guard-zone checks have been introduced. *)    
(*class boundsIntroductor  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor
 
    (* 
     * Contains list of pointer variables of a given function.
     *)
    val mutable ptrVarList = ref []

    (* 
     * Contains the list of statements in the sequence, that
     * should appear as a function body after transformation
     * It is created from existing statements of a function
     * plus statements initializing the lower and upper bound
     * variables
     *)
    val mutable stmtList = ref []

    (*
     * Contains list of formal parameters of a given function.
     * Used to check if a given pointer variable is a formal param,
     * if yes, then we don't introduce bounds for it.
     * If no, then we introduce bounds for it.
     *)
    val mutable formalParamList = ref []

    (* 
     * Boolean to check if bound variables are initialized.
     * bound variables needs to be initialized only at the start
     * of a function
     *)
    val mutable areBndsInit = ref false

    (* -----------------------------------------------------
     * This section contains methods of this class which
     * are used subsequentially in the other methods of this
     * class
     * ----------------------------------------------------- 
     *)

    (*
     * Generates a list of lower and upper bound variables.
     * varList is a list of string, where each string is a 
     * name of a pointer variable of a function.
     * bndVarList is a list of varinfo objects, where each
     * varinfo object corresponds to bound variable.
     *)
    method private genLoHiBndVarList (varList) (bndVarList) =
        match varList with
        var::vars -> (self#genLoHiBndVarList vars
        (bndVarList@
        (* low and high bounds are of unsigned int type *)
        [(genLoBndVInfo var)]@
        [(genHiBndVInfo var)]))
        | [] -> bndVarList

    (*
     * Introduces bound variables and the statements that initializes
     * them into a function.
     *)
    method private introduceBoundVars (currFunc : fundec) : fundec =
        begin
            begin
            (* 
             * add declarations for lower and upper bound variables
             * into given function by modifying slocals field of a
             * function
             *)
            currFunc.slocals <- (List.append (self#genLoHiBndVarList !ptrVarList []) currFunc.slocals); 

            (* 
             * Set smaxid field of func to current value + no of added local
             * variables
             *)
            currFunc.smaxid <- currFunc.smaxid + (2 * (List.length !ptrVarList));

            (* 
             * modify statements in the body of a function by new statements.
             *)
            currFunc.sbody.bstmts <- !stmtList;
            currFunc;
            end
        end

    (* -----------------------------------------------------------
     * This section contains over-ridden methods of nopCilVisitor
     * which direct the bounds introduction.
     * -----------------------------------------------------------
     *)

    (* 
     * vvdec is over-ridden to find out all local variables declared
     * inside a function. From this, we will find out which are pointer
     * variables.
     *)
    method vvdec (currVar : varinfo) : varinfo visitAction =
        begin
          let currtype = (Cil.unrollTypeDeep currVar.vtype)
          in
          match currtype with
          | TPtr(t1, _) -> begin
              (* 
               * if type is 1D pointer and it is not a formal param, 
               * then add it to the list of pointer variables
               *)
              match t1 with
              TPtr(_, _) -> SkipChildren
              | _ -> begin
                if(not (isFormalParam currVar !formalParamList))
                then  
                    ptrVarList := (List.append !ptrVarList [currVar.vname]);
                SkipChildren;
              end
          end
          | TComp(ci, _) -> begin
              (* 
               * TComp case is to take care of pointers that are 
               * transformed into gz_type struct by transformation
               * phase. 
               *
               * So if there is a declaration such as
               * char* p = ...
               * .. = &p;
               *
               * p is transformed into a gz_p,
               * where type of gz_p is something like
               *
               * struct {
               *    front_guardzone
               *    char* orig_p;
               *    rear_guardzone
               * }
               *
               * We need to be able to detect that, originally, p was
               * pointer and that it is not a formal param.
               *
               * We won't introduce bounds for such a variable since it's
               * address is taken, and hence it's aliased.
               *)
              SkipChildren
          end
          | _ -> SkipChildren
        end

    (* 
     * vfunc is over-ridden to be able to initialize stmtList and
     * pointer variable list to [] for each function.
     * And also to introduce bound variables into a function at the
     * end of it.
     *)
    method vfunc (currFunc : fundec) : fundec visitAction = 
        begin
            (* initialize variables local to a class *)
            (* clear stmtList of previous function, if any *)
            stmtList := []; 

            (* Clear pointer variables list of previous function, if any *)
            ptrVarList := [];

            (* initialize areBndsInit to false for current function *)
            areBndsInit := false;

            (* Copy formals of a current function to list *)
            formalParamList := currFunc.sformals;

            (* 
             * After processing of children of current function is done,
             * call introduceBoundVars to add bound variables and their
             * initialization statements to the body of current function.
             *)
            ChangeDoChildrenPost (currFunc, self#introduceBoundVars);
        end

        (* 
         * vstmt is over-ridden to add bound initialization 
         * statements to stmtList in correct order.
         * To be precise, we want to add bound initialization
         * statements after "Call ensure_sframe_guard_map()" and before any other statement.
         *
         * We do this by maintaining a list of statements in stmtList.
         * So idea is,
         *
         * if a current statement is not "Call ensure_sframe_guard_map", then 
         * if bound variables are not added to stmtList,
         *    add bound variables to stmtList
         * else
         *    simply add current stmt to stmtList
         *
         * if current statement is "Call ensure_sframe_guard_map" then
         * add it to stmtList, and then add bound variable initialization stmts
         * to stmtList
         *)
        method vstmt (currStmt : stmt) : stmt visitAction =
        (* 
         * Generate a statement to initialize bound variables.
         * precisely, generate a statement like
         * p_lo = 0U;
         *
         * lower and upper bound set to 0, indicate that bound
         * variables are currently invalid.
         *)
        let genBndInitStmt (bndVar : varinfo) : stmt =
            (Cil.mkStmt (Instr([(Set((Var(bndVar), NoOffset),
            Const(CInt64((Int64.of_int 0),
            IUInt,None)), locUnknown))])))
        in
        (*
         * Generate a list of statements that initializes
         * all the bound variables of a function.
         *)
        let rec genBndInitStmts (bndVarList) (initStmts) =
            match bndVarList with
            bndVar::bndVars -> [genBndInitStmt bndVar]@(genBndInitStmts bndVars
            initStmts)
            | [] -> initStmts
        in
        (*
         * add statements that initializes bound variables
         * to original statements of a function body.
         *)
        let addBndInitStmts (currStmt) =
            begin
                let bndVarList = (self#genLoHiBndVarList !ptrVarList [])
                in
                stmtList := (List.append !stmtList (genBndInitStmts bndVarList []));
                areBndsInit := true;
                stmtList := (List.append !stmtList [currStmt]);
            end
        in
        begin
            (* 
             * If statements that initialize bound variables are not added
             * to the original statements of a function body.
             *)
            if(not !areBndsInit) then
                begin
                match currStmt.skind with
                (* 
                 * we want to add bound initialization statements after
                 * ensure_sframe_guard_map call.
                 *)
                Instr(instrLst) -> begin
                                   match (List.hd instrLst) with
                                   Call(_,Lval(Var(func), _),_,_) -> begin
                                   if(func.vname = "ensure_sframe_guard_map") then
                                      stmtList := (List.append !stmtList [currStmt])
                                   else (addBndInitStmts currStmt)
                                      end
                                   | _ -> (addBndInitStmts currStmt)
                                   end
                | _ -> (addBndInitStmts currStmt)
                end
            else
                stmtList := (List.append !stmtList [currStmt]);
            SkipChildren;
        end
    
    (*  
     *  The objective of the current method is to filter out the functions
     *  that will be then instrumented.
     *)
     method vglob (currGlob : global) : global list visitAction =
         (* 
          * If the function is allowed to be instrumented,
          * then we go ahead and instrument it.
          * otherwise we skip it's instrumentation.
          *
          * We are introducing bounds for pointers local to a function,
          * so we filter out non-function Globals.
          *)
         if (permitInstrumentation currGlob) then
             match currGlob with
            | GFun(func, _) -> begin
                    if((skipFunction func.svar.vname file_name)) then
                        SkipChildren
                    else DoChildren
                    end
            | _ -> SkipChildren
         else
            SkipChildren
    end *)

(*===========================================================================*)
(*
 * NOTE: This analysis is not used currently.
 *)
(* 
 * The objective of this class to introduce statements in the source program to
 * update pointer bound information at all the places where a pointer is
 * updated.
 *
 * e.g. if in "char* p"; p has lower and upper bounds, then for a statement of
 * the form p = &obj;
 * This class will introduce statements such as
 * p_lo = &obj; p_hi = ( char* )&a + sizeof(obj);
 *)
(*class boundsTracker  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    (*
     * Contains list of formal parameters of a given function.
     * Used to check if a given pointer variable is a formal param,
     * if yes, then we don't introduce bounds for it.
     * If no, then we introduce bounds for it.
     *)
    val mutable formalParamList = ref []

    val mutable isTransformedFunc = ref false

    (* 
     * vinst is over-ridden to introduce statements for updating
     * bounds whenever there is an assignment to pointer.
     * e.g. if in "char* p"; p has lower and upper bounds, then for a statement of
     * the form p = &obj;
     * This class will introduce statements such as
     * p_lo = &obj; p_hi = ( char* )&a + sizeof(obj);
     *)
    method vinst (currInst : instr) : instr list visitAction =
        let dummyexpr = Const(CStr(""))
        in
        let rec isValidExprForBnds (expr : exp) : (exp * bool) =
            match expr with
            Const(_) -> (dummyexpr, false)
            | Lval(lvalue) -> begin
                match lvalue with
                (Var(vinfo), _) -> begin 
                                  if(is1DPtrVar lvalue) then
                                    (expr, true)
                                  else
                                    (dummyexpr, false)
                                  end
                | (Mem(expr1), _) -> (dummyexpr, false)
            end
            | SizeOf(_) -> (dummyexpr, false)
            | SizeOfE(expr1) -> (isValidExprForBnds expr1)
            | SizeOfStr(_) -> (dummyexpr, false)
            | AlignOf(_) -> (dummyexpr, false)
            | AlignOfE(expr1) -> (isValidExprForBnds expr1)
            | UnOp(_, expr1, _) -> (isValidExprForBnds expr1)
            | BinOp(_, expr1, expr2, _) -> begin
                let rexpr1, ret1 = (isValidExprForBnds expr1)
                in
                let rexpr2, ret2 = (isValidExprForBnds expr2)
                in
                if(ret1 = ret2) then
                    (dummyexpr, false)
                else if((ret1 = false) && (ret2 = true)) then
                    (rexpr2, ret2)
                else (*if((ret1 = true) and (ret2 = false)) then *)
                    (rexpr1, ret1)
            end
            | CastE(_, expr1) -> (isValidExprForBnds expr1)
            | AddrOf(_) -> (expr, true)
            | StartOf(_) -> (expr, true)
        in
        let genLoBndSetInst (name : string) (expr : exp) : instr =
          (Set((Var((genLoBndVInfo name)), NoOffset), expr, locUnknown))
        in
        let genHiBndSetInst (name : string) (expr : exp) : instr =
          (Set((Var((genHiBndVInfo name)), NoOffset), expr, locUnknown))
        in
        let genResetLoHiInsts (name : string) : instr list =
            [genLoBndSetInst name (Const(CInt64((Int64.of_int 0), IUInt,None)))]@
            [genHiBndSetInst name (Const(CInt64((Int64.of_int 0), IUInt,None)))]
        in
        let rec getFieldNames (off : offset) : string =
            match off with
            NoOffset -> ("")
            | Field(fldInfo, off) -> (fldInfo.fname ^ (getFieldNames off))
            | Index(expr, off) -> (getFieldNames off)
        in
        let rec getCompleteName (lvalue : lval) : string =
            match lvalue with
            (Var(vinfo), off) -> ((vinfo.vname) ^ (getFieldNames off))
            | (Mem(_),_) -> ""
        in
        let exprForZero = (Const(CInt64((Int64.of_int 0), IUInt,None)))
        in
        let getLoHiBndExpr (rexpr : exp) : exp list =
          begin
            match rexpr with
            Lval((Var(rvinfo), off)) -> begin
                if(is1DPtrVar (Var(rvinfo), off)) then
                  ([(Lval((Var((genLoBndVInfo (getCompleteName 
                  (Var(rvinfo),off)))), NoOffset)))]@
                  [(Lval((Var((genHiBndVInfo (getCompleteName
                  (Var(rvinfo),off)))), NoOffset)))])
                else
                  ([exprForZero]@[exprForZero])
                end
            | AddrOf(rlvalue) -> begin
                match rlvalue with
                (Var(rvinfo), off) -> begin
                  
                  let rec getLastField (off : offset) : (offset *
                  bool) =
                  match off with 
                  NoOffset -> (off,false)
                  | Field(_, off1) -> 
                    let oret, ret = (getLastField off1) in
                    begin
                    if(ret = false) then
                      (off, true)
                    else
                      (oret, ret)
                    end
                  | Index(_,off1) -> (getLastField off1)
                  in
                  
                  let oret, ret = (getLastField off) in
                    if(ret = true) then
                    begin
                      match oret with
                      
                      Field(finfo,_) -> begin
                      match finfo.ftype with
                      TArray(_,Some(Const(CInt64(maxd,_,_))),_) ->
                      begin
                        let noff,ooff = (Cil.removeOffset off) in
                        let nlrexpr = AddrOf(Var(rvinfo), (Cil.addOffset
                          (Index (Const (CInt64 ((Int64.of_int 0), IInt, None)),
                          NoOffset)) noff)) in
                        let nhrexpr = AddrOf(Var(rvinfo), (Cil.addOffset
                          (Index (Const (CInt64 (maxd, IInt, None)),
                          NoOffset)) noff)) in
                        ([nlrexpr]@[nhrexpr]) 
                      end
                      | _ -> begin
                        ([rexpr]@[(BinOp(PlusPI, (Cil.mkCast
                        rexpr (Cil.charPtrType)),
                        SizeOfE(Lval(rlvalue)), TInt(IUInt, [])))])
                      end
                      end
                      
                      | _ -> ([exprForZero]@[exprForZero])
                    end
                    else 
                      begin
                        ([rexpr]@
                        [(BinOp(PlusPI, (Cil.mkCast
                        rexpr (Cil.charPtrType)),
                        SizeOfE(Lval(rlvalue)), TInt(IUInt, [])))]) 
                      end
                  end
                  | (Mem(_),_) -> ([exprForZero]@[exprForZero])
                  end
                  | StartOf(rlvalue) -> begin
                             ([rexpr]@
                             [(BinOp(PlusPI, (Cil.mkCast
                              rexpr (Cil.charPtrType)),
                              SizeOfE(Lval(rlvalue)), TInt(IUInt, [])))]) 
                    end
                  | _ -> ([exprForZero]@[exprForZero])
            end
        in
        (*
         * This function returns true if expression contains formal parameter
         * for which bound information is available.
         *)
        let isExprContainsFormalPtrParam (rexpr : exp) (fpList : varinfo list) :
            bool =
            match rexpr with
            Lval((Var(rvinfo), off)) -> begin
                    if(isFormalParam rvinfo fpList) then
                        true
                    else
                        false
                    end
            | _ -> false
        in
        let isExprContainsGlobalPtrParam (rexpr : exp) : bool =
            match rexpr with
            Lval((Var(rvinfo), _)) -> (rvinfo.vglob)
            | _ -> false
        in
        let rec genBndTrackInsts (lvalue : lval) (expr : exp) : instr list =
            match lvalue with
            (Var(v), _) -> begin
                (*
                 * If current function is not a transformed function,
                 * and lvalue of assignment is formal param, then don't
                 * introduce bound variables for it
                 *)
                if(((not !isTransformedFunc) &&
                   (isFormalParam v !formalParamList)) || 
                   (isGlobalParam v))
                then [] 
                else 
                begin
                  let rexpr, ret = (isValidExprForBnds expr) in
                  begin
                    if(ret = false) then
                      (genResetLoHiInsts v.vname)
                    else 
                    begin
                      if(((not !isTransformedFunc) && 
                      (isExprContainsFormalPtrParam rexpr
                      !formalParamList)) ||
                      (isExprContainsGlobalPtrParam rexpr))
                      then
                        (genResetLoHiInsts v.vname)
                      else 
                      begin
                        let lohiexprs = (getLoHiBndExpr rexpr) in
                        [genLoBndSetInst v.vname (List.nth lohiexprs 0)]@
                        [genHiBndSetInst v.vname (List.nth lohiexprs 1)]
                      end
                    end
                  end
                end
            end
            | _ -> [] 
        in
        (* 
         * Introduce bound tracking assignment statements for 1D pointers
         * in a function
         *)
        let introBndAssignStmts (lvalue : lval) (expr : exp) : instr list =
          begin
              (* If lvalue is not a 1D pointer, then dont add any new
               * instructions
               *)
              if(not (is1DPtrVar lvalue)) then
                  []
              (* If lvalue is 1D pointer, then check expr and add corresponding 
               * instructions.
               *)
              else
                (genBndTrackInsts lvalue expr)
          end
        in
        let transformCall (currInst : instr) (fpList : varinfo list) : instr =
            let rec isAtleastOnePtrWithBnds (fpList : varinfo list)
            (origExprList : exp list) (origFpList : varinfo list) (ret : bool) : bool =
                match fpList with
                fp::fps -> begin
                            match origExprList with
                            e::es -> 
                              begin
                                let rexpr,rret = (isValidExprForBnds e) in
                                if((is1DPtrVar(Var(fp),NoOffset)) && rret &&
                                   (not ((not !isTransformedFunc) &&
                                   (isExprContainsFormalPtrParam rexpr
                                   origFpList))) &&
                                   (not (isExprContainsGlobalPtrParam rexpr)))
                                then (isAtleastOnePtrWithBnds fps es origFpList true)
                                else (isAtleastOnePtrWithBnds fps es origFpList ret)
                              end
                            | _ -> (ret)
                           end
                | _ -> (ret)
            in 
            let getTransformedExprList (fpList : varinfo list) (origExprList : exp
            list) : (exp list * bool) =
                let rec iterFPListAndTransExpr (fpList : varinfo list) (origExprList
                : exp list) (origFpList : varinfo list) (transExprList : exp list) : exp list =
                match fpList with
                fp::fps -> begin
                            match origExprList with
                            e::es -> 
                            begin
                              let rexpr,ret = (isValidExprForBnds e) in
                              if((is1DPtrVar(Var(fp),NoOffset)) && ret &&
                                 (not ((not !isTransformedFunc) &&
                                 (isExprContainsFormalPtrParam rexpr
                                 origFpList))))
                              then (iterFPListAndTransExpr fps es origFpList
                                   (transExprList@[e]@(getLoHiBndExpr rexpr)))
                              else if(is1DPtrVar(Var(fp),NoOffset))
                              then
                                   (iterFPListAndTransExpr fps es origFpList
                                   (transExprList@[e]@[exprForZero]@[exprForZero]))
                              else
                                   (iterFPListAndTransExpr fps es origFpList (transExprList@[e]))
                            end
                           | [] -> (transExprList)
                           end
                | [] -> (transExprList)
                in
                begin
                  let ret = (isAtleastOnePtrWithBnds fpList origExprList
                  !formalParamList false) 
                  in
                  if(ret)
                  then ((iterFPListAndTransExpr fpList origExprList !formalParamList []), true)
                  else ([], false)
                end
            in
            begin
            match currInst with
            Call(ret,Lval(Var(vinfo),off),expr_list, _) -> begin
                let rexpr_list, rret = (getTransformedExprList fpList expr_list) 
                in
                if(rret) then
                    let tvinfo = (Cil.copyVarinfo vinfo "") in
                    begin
                    tvinfo.vname <- (vinfo.vname ^ trans_func_bnd_suffix);
                    (Call(ret,Lval(Var(tvinfo),off),rexpr_list,locUnknown));
                    end
                else
                    (currInst)
            end
            | _ -> (currInst)
            end
        in
        let getMallocBnds (result : varinfo)(off : offset) (fname : varinfo) (args : exp list)
        : instr list =
                  ([(Set (((Var(genLoBndVInfo result.vname)), NoOffset), 
                         (Cil.mkCast (Lval(Var(result),off)) Cil.uintType), 
                         locUnknown))]@
                  [(Set ((Var((genHiBndVInfo result.vname)), NoOffset),
                         (Cil.mkCast (BinOp(PlusPI, (Cil.mkCast (Lval(Var(result),off))
                         Cil.charPtrType), (List.hd args), Cil.uintType)) Cil.uintType),
                         locUnknown))])
        in
        let getCallocBnds (result : varinfo)(off : offset) (fname : varinfo) (args : exp list)
        : instr list =
                  ([(Set (((Var(genLoBndVInfo result.vname)), NoOffset), 
                         (Cil.mkCast (Lval(Var(result),off)) Cil.uintType), 
                         locUnknown))]@
                  [(Set ((Var((genHiBndVInfo result.vname)), NoOffset),
                         (Cil.mkCast (BinOp(PlusPI, (Cil.mkCast (Lval(Var(result),off))
                         Cil.charPtrType), (BinOp (Mult, (List.nth args 0),
                         (List.nth args 1), Cil.uintType)), Cil.uintType)) Cil.uintType),
                         locUnknown))])
        in
        let getReallocBnds (result : varinfo)(off : offset) (fname : varinfo) (args : exp list)
        : instr list =
                  ([(Set (((Var(genLoBndVInfo result.vname)), NoOffset), 
                         (Cil.mkCast (Lval(Var(result),off)) Cil.uintType), 
                         locUnknown))]@
                  [(Set ((Var((genHiBndVInfo result.vname)), NoOffset),
                         (Cil.mkCast (BinOp(PlusPI, (Cil.mkCast (Lval(Var(result),off))
                         Cil.charPtrType), (List.nth args 1), Cil.uintType)) Cil.uintType),
                         locUnknown))])
        in
        begin
            match currInst with
            (*
             * If the instruction is assignment, then look for introducing
             * bound assignment statements for it under certain conditions.
             *)
            Set(lvalue, expr, _) -> begin 
                ChangeTo ([currInst]@(introBndAssignStmts lvalue expr));
            end
            (* 
             * If the instruction is Call, then we need to check if a pointer 
             * for which we have bounds, is used as an actual argument to call.
             * If it is used, then we need to reset low and high bounds for that
             * pointer as a function can modify pointee for that pointer.
             *)
            | Call(lval_opt,Lval(Var(vinfo),_),expr_list, _) -> begin
              let checkIfInterProcBoundTracking =
                if(not !dontDoInterProcBoundTracking) 
                then
                  if(Hashtbl.mem transFuncsTbl vinfo.vname)
                  then (ChangeTo [(transformCall currInst (Hashtbl.find
                      transFuncsTbl vinfo.vname))];)
                  else SkipChildren
                else SkipChildren
              in
              match lval_opt with
              Some(lvalue) -> begin
                match lvalue with
                (Var(result),off) -> begin
                  if(is1DPtrVar lvalue) &&
                    (not ((not !isTransformedFunc) &&
                      (isFormalParam result !formalParamList)))
                  then
                    if(vinfo.vname = "malloc") then
                      ChangeTo ([currInst]@(getMallocBnds result off vinfo
                      expr_list))
                    else if(vinfo.vname = "calloc") then
                      ChangeTo ([currInst]@(getCallocBnds result off vinfo
                      expr_list))
                    else if(vinfo.vname = "realloc") then
                      ChangeTo ([currInst]@(getReallocBnds result off vinfo
                      expr_list))
                    else
                      (checkIfInterProcBoundTracking)
                  else
                      (checkIfInterProcBoundTracking)
                  end
                | _ -> 
                      (checkIfInterProcBoundTracking)
                end
              | _ -> if(vinfo.vname = "free") then
                        let rec getLval (expr : exp) =
                            match expr with
                            CastE(_,expr) -> (getLval expr)
                            | Lval(Var(ptr), off) -> (ptr, off)
                            | _ -> ((Cil.makeVarinfo false "tmp" Cil.uintType),
                            NoOffset)
                        in
                        let matchFreeParam ((ptr : varinfo), (off : offset)) =  
                            if((is1DPtrVar (Var(ptr),off)) &&
                              (not ((not !isTransformedFunc) &&
                              (isFormalParam ptr !formalParamList))))
                            then
                                ChangeTo([currInst]@(genResetLoHiInsts
                                ptr.vname))
                            else
                               (checkIfInterProcBoundTracking)
                        in
                        (matchFreeParam (getLval (List.hd expr_list)))
                     else
                      (checkIfInterProcBoundTracking)
              end
            (* 
             * If the instruction is Asm, then we don't need to
             * introduce anything for it
             *)
            | _ -> SkipChildren 
        end

    method vfunc (currFunc : fundec) : fundec visitAction =
    let replaceIsCharGuardC (currFunc : fundec) : fundec =
      let genIfElBndChk (expr : exp) (icri : instr) : (stmt * bool) =
          begin
          match expr with
          Lval(Mem(Lval(Var(vinfo),off)),_) -> begin
              if((is1DPtrVar (Var(vinfo), off)) &&
                 (not ((not !isTransformedFunc) && 
                 (isFormalParam vinfo !formalParamList))) &&
                 (not (isGlobalParam vinfo)))  then
              begin
                Cil.useLogicalOperators := true;
                let if_block = (Cil.mkBlock 
                [(Cil.mkStmt (If(
                  BinOp(LOr, 
                  (BinOp(Lt, (Cil.mkCast (Lval(Var(vinfo), NoOffset)) 
                  Cil.uintType), 
                  Lval(Var(genLoBndVInfo vinfo.vname), NoOffset), Cil.intType)),
                  
                  (BinOp(Gt,(Cil.mkCast (BinOp(PlusPI, (Cil.mkCast (Lval(Var(vinfo), NoOffset)) 
                  Cil.charPtrType), (SizeOfE expr), Cil.uintType)) Cil.uintType),
                  Lval(Var(genHiBndVInfo vinfo.vname), NoOffset), Cil.intType)), 
                  Cil.intType), 

                  (Cil.mkBlock ([getPrtStmt file_name]@[(Cil.mkStmtOneInstr (Call(None, Lval(
                  (Var(Cil.makeVarinfo false "abort" Cil.voidType)),
                  NoOffset), [], locUnknown)))])), 
                  
                  (Cil.mkBlock []), locUnknown)))])
                in
                let else_block = (Cil.mkBlock [(Cil.mkStmtOneInstr icri)]) 
                in
                ((Cil.mkStmt(If((BinOp(Ne, Lval(Var(genLoBndVInfo vinfo.vname), NoOffset),
                Const(CInt64((Int64.of_int 0), IUInt, None)), Cil.intType)), 
                if_block, else_block, locUnknown))), true)
              end
              else
                  ((Cil.mkEmptyStmt ()), false)
          end
          | _ ->  ((Cil.mkEmptyStmt ()), false)
          end
      in
      let rec modifyIsCharGuardCsToIE (insts : instr list) (instq : instr list) (rstmts : stmt list) :
          stmt list =
          match insts with
          cinst::ilist -> begin
                          match cinst with
                          Call(_,Lval(Var(fname), _),exprs,_) -> begin
                              if(fname.vname = "is_char_guard") then
                              let rstmt, ret = (genIfElBndChk (List.hd exprs)
                              cinst) in begin
                                if(ret = true) then
                                  let seqstmts = (Cil.mkStmt (Instr(instq)))
                                  in
                                  (modifyIsCharGuardCsToIE ilist [] (rstmts@[seqstmts]@[rstmt]))
                                else
                                  (modifyIsCharGuardCsToIE ilist (instq@[cinst]) rstmts)
                              end
                              else
                                (modifyIsCharGuardCsToIE ilist (instq@[cinst]) rstmts)
                          end
                          | _ -> (modifyIsCharGuardCsToIE ilist (instq@[cinst]) rstmts)
                        end
          | [] -> (rstmts @ [(Cil.mkStmt (Instr(instq)))])
      in
      let rec getTargetLabel(tLabel : label list) : string list =
          match tLabel with
          l::ls -> begin
              match l with
              Label(str,_,_) -> (*([str]@(getTargetLabel ls))*)
                                [str]
                | _ -> (getTargetLabel ls)
              end
          | [] -> []
      in
      let rec filterAndProcessInstr (stmts : stmt list) (newstmts : stmt list)
      (gotolabels : string list) : (stmt list * string list) =
        match stmts with
        currStmt::stmtlist -> begin
          match currStmt.skind with
          Instr(insts) ->
              let rstmts : stmt list = (modifyIsCharGuardCsToIE insts [] [])
              in
              begin
                (List.hd rstmts).labels <- currStmt.labels; 
                (filterAndProcessInstr stmtlist (newstmts@rstmts) gotolabels);
              end
          | If(exp,iblk,eblk,loc) -> 
              let newistmts,iglbls = (filterAndProcessInstr iblk.bstmts [] []) in
              let newestmts,eglbls = (filterAndProcessInstr eblk.bstmts [] []) in
              let tmpStmt = (Cil.mkStmt (If(exp,(Cil.mkBlock newistmts),
              (Cil.mkBlock newestmts),loc))) in
              begin
                tmpStmt.labels <- currStmt.labels;
                (filterAndProcessInstr stmtlist (newstmts@[tmpStmt])
                (gotolabels @ iglbls @ eglbls));
              end
          | Switch(exp,blk,stmt1,loc) ->
              let newblkstmts,blklbls = (filterAndProcessInstr blk.bstmts [] []) 
              in
              let newstmt1,stmtlbls = (filterAndProcessInstr stmt1 [] []) in
              let tmpStmt = (Cil.mkStmt (Switch(exp, (Cil.mkBlock
                  newblkstmts), newstmt1, loc))) in
              begin
                  tmpStmt.labels <- currStmt.labels;
                  (filterAndProcessInstr stmtlist (newstmts@[tmpStmt])
                  (gotolabels @ blklbls @ stmtlbls));
              end
          | Loop(blk,loc,stmt1,stmt2) -> 
              let newblkstmts,blklbls = (filterAndProcessInstr blk.bstmts [] []) 
              in
                  (* let newstmt1 = (filterAndProcessInstr [stmt1] []) in *)
                  (* let newstmt2 = (filterAndProcessInstr [stmt2] []) in *)
                  (* let tmpStmt = (Cil.mkStmt (Loop((Cil.mkBlock newblkstmts),
                  loc,newstmt1,newstmt2))) in *)
              let tmpStmt = (Cil.mkStmt (Loop((Cil.mkBlock newblkstmts),
                  loc,stmt1,stmt2))) in
              begin
                  tmpStmt.labels <- currStmt.labels;
                  (filterAndProcessInstr stmtlist (newstmts@[tmpStmt])
                  (gotolabels @ blklbls));
              end
              (*(filterAndProcessInstr stmtlist (newstmts@[currStmt])
              (gotolabels @ blklbls))*)
          | Block(blk) -> 
              let newblkstmts,blklbls = (filterAndProcessInstr blk.bstmts [] []) 
              in
              let tmpStmt = (Cil.mkStmt (Block((Cil.mkBlock newblkstmts)))) in
              begin
                  tmpStmt.labels <- currStmt.labels;
                  (filterAndProcessInstr stmtlist (newstmts@[tmpStmt])
                  (gotolabels @ blklbls));
              end
          | TryFinally(blk1,blk2,loc) ->
              let newblk1stmts,blk1lbls = (filterAndProcessInstr blk1.bstmts [] []) 
              in
              let newblk2stmts,blk2lbls = (filterAndProcessInstr blk2.bstmts [] []) 
              in
              let tmpStmt = (Cil.mkStmt (TryFinally((Cil.mkBlock
                  newblk1stmts), (Cil.mkBlock newblk2stmts), loc))) in
              begin
                  tmpStmt.labels <- currStmt.labels;
                  (filterAndProcessInstr stmtlist (newstmts@[tmpStmt])
                  (gotolabels @ blk1lbls @ blk2lbls));
              end
          | TryExcept(blk1,(inst1,exp),blk2,loc) ->
              let newblk1stmts,blk1lbls = (filterAndProcessInstr blk1.bstmts [] []) 
              in
              let newblk2stmts,blk2lbls = (filterAndProcessInstr blk2.bstmts [] []) 
              in
              let tmpStmt = (Cil.mkStmt (TryExcept((Cil.mkBlock newblk1stmts),
                  (inst1,exp),(Cil.mkBlock newblk2stmts),loc))) in
              begin
                  tmpStmt.labels <- currStmt.labels;
                  (filterAndProcessInstr stmtlist (newstmts@[tmpStmt])
                  (gotolabels @ blk1lbls @ blk2lbls));
              end
          | Goto(stmtref,_) -> 
              let tLabels = (getTargetLabel (!stmtref).labels) in
                  (filterAndProcessInstr stmtlist 
                  (newstmts@[currStmt]) (gotolabels@tLabels))
          | _ -> (filterAndProcessInstr stmtlist (newstmts@[currStmt]) gotolabels)
        end
          | [] -> (newstmts,gotolabels)
      in
      let rec patchGotos (newstmts : stmt list) (gotolabels : string list)
      (origstmts : stmt list) (patchedStmts : stmt list) : (stmt list * string
      list) =
          let rec getStmtwithLabel (origstmts : stmt list) (gotolabel : string) :
              (stmt * bool) =
            let rec isStmthasLabel (labels : label list) (gotolabel : string) :
                bool =
                match labels with
                  l::ls -> begin
                    match l with
                    Label(str,_,_) -> begin
                                  if(str = gotolabel) then
                                      true
                                  else
                                      (isStmthasLabel ls gotolabel)
                                 end
                    | _ -> (isStmthasLabel ls gotolabel)
                  end
                  | [] -> false
            in
            match origstmts with
            currstmt::stmts -> begin
                if(isStmthasLabel currstmt.labels gotolabel) then
                    (currstmt, true)
                else 
                match currstmt.skind with
                If(_,blk1,blk2,_) -> 
                    let rstmt1,ret1 = 
                        (getStmtwithLabel blk1.bstmts gotolabel) in
                    if(ret1) then
                      (rstmt1,ret1)
                    else
                       let rstmt2, ret2 = 
                           (getStmtwithLabel blk2.bstmts gotolabel) in
                       if(ret2) then
                        (rstmt2,ret2)
                       else
                        (getStmtwithLabel stmts gotolabel)
                | Switch(_,blk,stmtlst,_) ->
                    let rstmt1,ret1 = 
                        (getStmtwithLabel blk.bstmts gotolabel) in
                    if(ret1) then
                      (rstmt1,ret1)
                    else
                       let rstmt2, ret2 = 
                           (getStmtwithLabel stmtlst gotolabel) in
                       if(ret2) then
                        (rstmt2,ret2)
                       else
                        (getStmtwithLabel stmts gotolabel)
                | Loop(blk,_,stmt1,stmt2) ->
                    let rstmt1,ret1 = 
                        (getStmtwithLabel blk.bstmts gotolabel) in
                    if(ret1) then
                      (rstmt1,ret1)
                    (*else
                       let rstmt2, ret2 = 
                           (getStmtwithLabel [stmt1] gotolabel)
                       in
                       if(ret2) then
                        (rstmt2,ret2)
                       else
                           let rstmt3,ret3 = 
                               (getStmtwithLabel [stmt2] gotolabel) in
                           if(ret3) then
                               (rstmt3,ret3)*)
                           else
                               (getStmtwithLabel stmts gotolabel)
                | Block(blk) ->
                    let rstmt1,ret1 = 
                          (getStmtwithLabel blk.bstmts gotolabel) in
                     if(ret1) then
                        (rstmt1,ret1)
                     else
                        (getStmtwithLabel stmts gotolabel)
                | TryFinally(blk1,blk2,_) ->
                    let rstmt1,ret1 = 
                        (getStmtwithLabel blk1.bstmts gotolabel) in
                    if(ret1) then
                      (rstmt1,ret1)
                    else
                       let rstmt2, ret2 = 
                          (getStmtwithLabel blk2.bstmts gotolabel) in
                       if(ret2) then
                          (rstmt2,ret2)
                       else
                          (getStmtwithLabel stmts gotolabel)
                | TryExcept(blk1,_,blk2,_) ->
                    let rstmt1,ret1 = 
                        (getStmtwithLabel blk1.bstmts gotolabel) in
                    if(ret1) then
                      (rstmt1,ret1)
                    else
                       let rstmt2, ret2 = 
                           (getStmtwithLabel blk2.bstmts gotolabel) in
                       if(ret2) then
                          (rstmt2,ret2)
                       else
                          (getStmtwithLabel stmts gotolabel)
                | _ -> (getStmtwithLabel stmts gotolabel)
            end
            | [] -> ((Cil.mkEmptyStmt ()),false)
          in
          begin
            match newstmts with
              currstmt::stmts -> begin
                  match currstmt.skind with
                  Goto(stmtref,loc) -> begin
                      if(not (List.length gotolabels = 0)) then
                        begin
                            let rstmt,ret = (getStmtwithLabel origstmts ((List.hd
                        gotolabels))) in
                            stmtref := rstmt;
                          if(not ret) then
                              print_string "** Label not found ** ";
                          currstmt.skind <- Goto(stmtref,loc);
                          (patchGotos stmts (List.tl gotolabels) origstmts (patchedStmts@[currstmt]))
                        end
                      else
                          (patchGotos stmts gotolabels origstmts (patchedStmts@[currstmt]))
                  end
                  | If(expr,iblk,eblk,loc) ->
                      let piblk,iglbls = (patchGotos iblk.bstmts gotolabels origstmts []) 
                      in
                      let peblk,eglbls = (patchGotos eblk.bstmts iglbls origstmts []) 
                      in
                      currstmt.skind <-
                          (If(expr,Cil.mkBlock(piblk),Cil.mkBlock(peblk),loc));

                      (patchGotos stmts eglbls origstmts (patchedStmts@[currstmt]))
                  | Switch(expr,blk,stmtlist,loc) ->
                      let pblk,blbls = (patchGotos blk.bstmts gotolabels origstmts [])
                      in
                      let pstmts,slbls = (patchGotos stmtlist blbls origstmts [])
                      in
                      currstmt.skind <- (Switch(expr,(Cil.mkBlock
                      pblk),pstmts,loc));

                      (patchGotos stmts slbls origstmts (patchedStmts@[currstmt]))
                  | Loop(blk,loc,stmt1,stmt2) ->
                      let pblk,blbls = (patchGotos blk.bstmts gotolabels origstmts [])
                      in
                      currstmt.skind <- Loop((Cil.mkBlock
                      pblk),loc,stmt1,stmt2);

                      (patchGotos stmts blbls origstmts (patchedStmts@[currstmt]))
                  | Block(blk) ->
                      let pblk,blbls = (patchGotos blk.bstmts gotolabels origstmts [])
                      in
                      currstmt.skind <- Block(Cil.mkBlock pblk);

                      (patchGotos stmts blbls origstmts (patchedStmts@[currstmt]))
                  | TryFinally(blk1,blk2,loc) ->
                      let pblk1,blbls1 = (patchGotos blk1.bstmts gotolabels origstmts [])
                      in
                      let pblk2,blbls2 = (patchGotos blk2.bstmts blbls1 origstmts [])
                      in
                      currstmt.skind <- TryFinally((Cil.mkBlock
                      pblk1),(Cil.mkBlock pblk2),loc);

                      (patchGotos stmts blbls2 origstmts (patchedStmts@[currstmt]))
                  | TryExcept(blk1,(inst1,expr),blk2,loc) ->
                      let pblk1,blbls1 = (patchGotos blk1.bstmts gotolabels origstmts [])
                      in
                      let pblk2,blbls2 = (patchGotos blk2.bstmts blbls1 origstmts [])
                      in
                      currstmt.skind <- TryExcept((Cil.mkBlock
                      pblk1),(inst1,expr),(Cil.mkBlock pblk2),loc);

                      (patchGotos stmts blbls2 origstmts (patchedStmts@[currstmt]))
                  | _ -> (patchGotos stmts gotolabels origstmts (patchedStmts@[currstmt]))
              end
              | [] -> (patchedStmts,gotolabels)
          end
      in
      let stmts = currFunc.sbody.bstmts 
      in
      let newstmts,glabels = (filterAndProcessInstr stmts [] [])
      in
      let patchedstmts,glabels =
      if(not ((List.length glabels) = 0)) then
          (patchGotos newstmts glabels newstmts [])
      else
          (newstmts, [])
      in
    begin
    currFunc.sbody.bstmts <- patchedstmts;
    currFunc;
    end
    in
    (*
     *)
    begin
      (*if(currFunc.svar.vinline ||
         (currFunc.svar.vstorage = Static)) then
      begin*)
        if (not !isTransformedFunc)
        (* Copy formals of a current function to list *)
        then (formalParamList := currFunc.sformals;)
        else formalParamList := [];

        ChangeDoChildrenPost(currFunc, replaceIsCharGuardC);
      (*end
      else
        SkipChildren;*)
    end

    (*  
     *  The objective of the current method is to filter out the functions
     *  that will be then instrumented.
     *)
     method vglob (currGlob : global) : global list visitAction =
         let rec fillSlocalinHT (slocals : varinfo list) =
              match slocals with
              l::ls -> if((isLoBndSuffix l.vname) ||
                          (isHiBndSuffix l.vname)) then
                           (Hashtbl.add varinfoHT l.vname l);
                       (fillSlocalinHT ls)
              | [] -> ()
         in
         (* 
          * If the function is allowed to be instrumented,
          * then we go ahead and instrument it.
          * otherwise we skip it's instrumentation.
          *
          * We are introducing bounds for pointers local to a function,
          * so we filter out non-function Globals.
          *)
         if (permitInstrumentation currGlob) then
             match currGlob with
            | GFun(func, _) -> begin
                    if(not !dontDoInterProcBoundTracking) then
                      if(isBndTransFunc func.svar.vname) 
                      then (isTransformedFunc := true;)
                      else isTransformedFunc := false;

                    (Hashtbl.clear varinfoHT);
                    (fillSlocalinHT(func.slocals));
                    
                    if((skipFunction func.svar.vname file_name))
                    then (SkipChildren;)
                    else DoChildren;
                    end
            | _ -> SkipChildren
         else
            SkipChildren
    end
*)
(*===========================================================================*)
(*
 * NOTE: This analysis is not used currently.
 *)
(*type rdRetcode = NO_RD_INFO_AVAILABLE
                 | ERROR_RD_PROCESSING
                 | ALL_RD_SET_ZERO 
                 | ALL_RD_SET_NONZERO 
                 | ALL_RD_SET_ZERO_NONZERO

class eliminateGZChecks  (f:file) (file_name:string) =
    object (self)
        inherit nopCilVisitor

    (*
     * return -1 if none of the following applies
     * return 1 if all assignments are 0
     *        2 if all assignments are non-zero
     *        3 if some are zero and some are non-zero
     *)
    method private isStmtSetBndToZero (currStmt : stmt) (lbvinfo : varinfo) :
        rdRetcode =
      let rec isInstrsSetLoBndZero (ilist : instr list) (lbvinfo : varinfo)
      (currStmt : stmt) : rdRetcode =
          match ilist with
            inst::insts -> begin
              match (inst) with
              Set((Var(vinfo),_),expr,_) ->
                  if(vinfo.vname = lbvinfo.vname) then
                      match expr with
                      Const(CInt64(i,_,_)) ->
                        if((i64_to_int i) = 0)
                        then ALL_RD_SET_ZERO
                        else ALL_RD_SET_NONZERO
                      (*
                       * there might be an assignment of the form,
                       * p_lo = q_lo;
                       * in such a case, we need to find out the RDs
                       * for q_lo and check if q_lo can be 0 at such
                       * a statement
                       *)
                      | Lval(Var(bvinfo),_) ->
                          if(not (vinfo.vname = bvinfo.vname)) then
                          let rds : (unit * int * IOS.t IH.t) option = 
                              (Reachingdefs.getRDs currStmt.sid) 
                          in
                          begin (*
                          print_string "\n2. var = ";
                          print_string vinfo.vname;
                          print_string " bvar = ";
                          print_string bvinfo.vname;
                          print_string "stmt id = ";
                          (print_string (string_of_int currStmt.sid));
                          print_string "\n";*)
                          (self#processBndAssign rds bvinfo)
                          end
                          else
                            ALL_RD_SET_NONZERO
                      | _ -> ALL_RD_SET_NONZERO
                  else
                      (isInstrsSetLoBndZero insts lbvinfo currStmt)
              | _ -> (isInstrsSetLoBndZero insts lbvinfo currStmt)
            end
            | [] -> NO_RD_INFO_AVAILABLE
       in
      match currStmt.skind with
      Instr(ilist) -> (isInstrsSetLoBndZero (List.rev ilist) lbvinfo currStmt)
      | _ -> NO_RD_INFO_AVAILABLE

    method private processDefs (defs : IOS.elt list) (lbvinfo : varinfo)
    (retCode : rdRetcode) : rdRetcode =
      match defs with
      def_id_opt::def_id_opt_list -> begin
        match def_id_opt with
          Some(def_id) ->
            let stmt_opt = (Reachingdefs.getDefIdStmt def_id)
            in
            begin
              match stmt_opt with
                None -> (self#processDefs def_id_opt_list lbvinfo retCode)
                | Some(cstmt) -> begin
                    let tmpRetCode = (self#isStmtSetBndToZero cstmt lbvinfo) in
                    if((not (retCode = NO_RD_INFO_AVAILABLE)) && 
                       (not (retCode = ALL_RD_SET_ZERO_NONZERO))) then
                           if(((retCode = ALL_RD_SET_ZERO) && 
                               (tmpRetCode = ALL_RD_SET_NONZERO)) ||
                              (retCode = ALL_RD_SET_NONZERO) && 
                              (tmpRetCode = ALL_RD_SET_ZERO)) then
                            (self#processDefs def_id_opt_list lbvinfo
                            ALL_RD_SET_ZERO_NONZERO)
                           else
                            (self#processDefs def_id_opt_list lbvinfo tmpRetCode)
                    else
                        (self#processDefs def_id_opt_list lbvinfo retCode)
                end
            end
          | _ -> (self#processDefs def_id_opt_list lbvinfo retCode)
        end
      | [] -> (retCode)


    (*
     * return 0 if all assignments are 0
     *        1 if all assignments are non-zero
     *        2 if some are zero and some are non-zero
     *)
    method private processBndAssign (rds : ((unit * int * IOS.t IH.t) option)) 
    (lbvinfo : varinfo) : rdRetcode =
        match rds with 
        None -> (NO_RD_INFO_AVAILABLE)
        | Some(_,_,iosh) ->
            let def_id_set_opt : IOS.t option =
              (Reachingdefs.iosh_lookup iosh lbvinfo) in
            match def_id_set_opt with
              Some(def_id_set) -> 
                      let defs : IOS.elt list = (IOS.elements def_id_set) in
                      (self#processDefs defs lbvinfo ERROR_RD_PROCESSING)
              | None -> (NO_RD_INFO_AVAILABLE)
    
    method private isBndCheck (expr : exp) : (varinfo * bool) =
        match expr with
          BinOp(op,Lval(Var(vinfo),_),
                Const(CInt64(i,_,_)),_) -> 
                                    if((op = Ne) && 
                                    (isLoBndSuffix vinfo.vname) &&
                                    ((i64_to_int i) = 0))
                                 then (vinfo, true)
                                 else ((Cil.makeVarinfo false "tmp"
                                 Cil.voidType), false)
          | _ -> ((Cil.makeVarinfo false "tmp" Cil.voidType), false)

    method vstmt (currStmt : stmt) : stmt visitAction = 
    match currStmt.skind with
       If(expr,iblk,eblk,loc) -> begin
        let vinfo, bret = (self#isBndCheck expr) in
        if(bret) then
          begin
                (*
                          print_string "\n2. var = ";
                          print_string vinfo.vname;
                          print_string " bvar = ";
                          (print_string (string_of_int currStmt.sid));
                          print_string "\n";
                 *)
          let rds : (unit * int * IOS.t IH.t) option = 
              (Reachingdefs.getRDs currStmt.sid) in
          let ret = (self#processBndAssign rds vinfo) in
            begin            
                (*print_string "  \n ******";
              print_string "For variable:";
              print_string vinfo.vname;
              print_string " ";
              print_string (string_of_int ret);
              print_string " ****** \n";*)
              if((ret = ALL_RD_SET_ZERO) || (ret = ALL_RD_SET_ZERO_NONZERO)) then
                  (currStmt.skind <- ((List.hd eblk.bstmts).skind))
              else if(ret = ALL_RD_SET_NONZERO) then
                  (*(currStmt.skind <- If(expr,iblk,(Cil.mkBlock []),loc))*)
                  (currStmt.skind <- ((List.hd iblk.bstmts).skind))
              else
                  (*(currStmt.skind <- ((List.hd eblk.bstmts).skind))*)
                  ()
            end
            ; DoChildren
         end
        else
            DoChildren
       end
       | Switch(_,_,_,_) -> DoChildren
       | Loop(_,_,_,_) -> DoChildren
       | Block(_) -> DoChildren
       | TryFinally(_,_,_) -> DoChildren
       | TryExcept(_,_,_,_) -> DoChildren
       | _ -> SkipChildren


    (*method vvdec (currVar : varinfo) : varinfo visitAction =
        (print_string currVar.vname;);
        (print_string "  ";);
        (print_string (string_of_int currVar.vid););
        (print_string " \n ";);
        SkipChildren*)

    method vfunc (currFunc : fundec) : fundec visitAction =
        let _ = Cfg.clearCFGinfo currFunc in
        let _ = Cfg.cfgFun currFunc in
        (*let _ = Cfg.printCfgFilename "/tmp/tt" currFunc in*)
        begin
            (*try *)
                (Reachingdefs.computeRDs currFunc);
                DoChildren
            (*with _ -> print_string "Screwed Up!!!\n\n"; SkipChildren;*)
        end

    (*  
     *  The objective of the current method is to filter out the functions
     *  that will be then instrumented.
     *)
     method vglob (currGlob : global) : global list visitAction =
         (* 
          * If the function is allowed to be instrumented,
          * then we go ahead and instrument it.
          * otherwise we skip it's instrumentation.
          *
          * We are introducing bounds for pointers local to a function,
          * so we filter out non-function Globals.
          *)
         if (permitInstrumentation currGlob) then
             match currGlob with
            | GFun(func, _) -> begin
                    if((skipFunction func.svar.vname file_name) ||
                       (func.svar.vinline = true) ||
                       (func.svar.vstorage = Static)) 
                    then SkipChildren
                    else DoChildren
                    end
            | _ -> SkipChildren
         else
            SkipChildren
    end *)

(*===========================================================================*)
let init_log (currFile : file) : unit = 
    begin
        log line
    end

let terminate_log (filename : string) : unit =
    let flag_perm = [Open_append; Open_creat; Open_text]
    (*  Note : This is extremely important. Here it is assumed filename is the complete
     *  file path *)
    and file_name = filename ^ log_suffix 

    in
    begin
        (*  Open a file by name currFilename.log*)
        let log_channel =   (open_out_gen flag_perm log_file_perm 
                            file_name)
        in
        if (!Errormsg.debugFlag) then
            Pretty.fprint log_channel log_width !log_doc
    end


(*  The basic objective of this method is to read in all the names
 *  provided in the specified file and put it into a list.
 *)
let read_file (file_name: string) : string list =
    let symbols_list = ref []
    in

    begin
        if file_name = "" then
                log (text "No File to read.")
        else
            begin
                try (
                    let input_channel = open_in file_name
                    in
                    begin
                        while true do
                            let symbol_name = (input_line input_channel)
                            in
                            begin
                                symbols_list := symbol_name ::
                                    !symbols_list;
                                log (text ("Name read : " ^ symbol_name))
                            end
                        done;
                        ()
                    end
                ) with
                |   Sys_error(message) -> 
                        begin
                            log (text message);
                            log (text (file_name ^ " file could not be opened"))
                        end
                |   End_of_file -> 
                            log(text (file_name ^ " file list read successfully"))
            end;
        !symbols_list
    end

(*  The basic objective of this method is to read in all the names
 *  provided in the specified functions file and put it into a list.
 *  On every line of the function file, either a single function name will be
 *  provided or a function name AND a list of line number ranges.
 *  The following are the two formats acceptable to this parser
 *  function_name_01
 *  function_name_02 (1,2) (3,4)
 *)
let read_functions_file (file_name: string) : unit =
    begin
        if file_name = "" then
                log (text "No File to read.")
        else
            begin
                try (
                    let input_channel = open_in file_name

                    (*  Basically this regular expression gets the first word
                     *  which is supposed to the function name.
                     * *)
                    and func_name_regex = (Str.regexp "[ \t]*\\([a-zA-Z0-9_]+\\)[ \t$]*")

                    (*  This is the regular expression for the line ranges to be
                     *  specified for the function. Note that these must be in
                     *  the format (num1,num2).
                     * *)
                    and line_range_regex = Str.regexp 
                    "([ \t]*\\([0-9]*\\)[ \t]*,[ \t]*\\([0-9]*\\)[ \t]*)[ \t$]*"
                    in

                    (*  We will use this recursive function to obtain the list
                     *  of line ranges from current line. Note that this is the
                     *  original string with the index from where to begin the
                     *  new search
                     * *)
                    let rec match_line_range (curr_line : string) (index : int): 
                                        (int*int)list =
                        begin
                            if (Str.string_match line_range_regex curr_line
                                    index ) then
                                begin
                                    let new_index = Str.match_end ()
                                    and first_int = (Str.matched_group 1
                                                        curr_line)
                                    and second_int = (Str.matched_group 2
                                                    curr_line)
                                    in
                                    
                                    begin
                                    
                                        log (text ("Line range added : (" ^
                                        first_int ^ " , " ^ second_int ^ ")"));

                                        ((int_of_string first_int),(int_of_string
                                            second_int)) :: (match_line_range
                                            curr_line new_index )
                                    end
                                end
                            else
                                (*  This indicates that no further line ranges
                                 *  were found.
                                 *  Return an empty list
                                 *  *)
                                []               
                        end
                    in

                    begin
                        (*  Note that we will have to loop here to read all the
                         *  lines of the file.
                         * *)
                        while true do
                            let curr_line = (input_line input_channel)
                            in
                            begin
                                if (Str.string_match func_name_regex
                                        curr_line 0 ) then
                                    begin
                                        let func_name = (Str.matched_group 1
                                                curr_line )
                                        and end_index = (Str.match_end () )                                        
                                        in

                                        let range_list = (match_line_range
                                                    curr_line end_index)
                                        in
                                        
                                        begin
                                            log (text ("Function added to functions_list: " ^
                                                func_name));
                                            (Hashtbl.add functions_list
                                                    func_name range_list)
                                        end
                                    end
                                else
                                    (*  This option implies that there was no
                                     *  substring that matched function name
                                     *  regular expression
                                     * *)
                                     log (text ("Line ignored : " ^ curr_line))
                            end
                        done;
                        ()
                    end
                ) with
                |   Sys_error(message) -> 
                        begin
                            log (text message);
                            log (text (file_name ^ " file could not be opened"))
                        end
                |   End_of_file -> 
                            log(text (file_name ^ " file list read successfully"))
            end;
    end

(*  Note that we usually have a problem as CIL preprocesses a file and
 *  therefore we cannot include a header file in the files we want to include
 *  because of the danger of having same definition twice and thus errors.
 *  
 *  The basic objective of this function is to go through the list of current
 *  global elements to see which extra header files we need to include for our
 *  purpose.
 *  Currently we will handle ONLY variable declarations, definitions,
 *  function declarations and typedefs
 * *)
  
 (*  The basic objective of this method is to generate a list of all the header files
  *  that are needed by our files but are not present in the current file
  *  being processed.
  * *)
    let include_files (currGlobals : global list) : global list =

        let needed_header_files = ref ([] : global list)
        
        in
        (*  The basic idea of this function is to process current header tuple
         *  to see if the specified global element is present in the current
         *  file. If it is not, then include the specified header file in the
         *  file list defined above (i.e., needed_header_files).
         * *)
        let process_include_tuple (currTuple : (string * string)) 
                            : unit =
            let element_name = fst currTuple
            and header_file = snd currTuple

            in
            let element_exists (currGlob : global) : bool =
                match currGlob  with
                |   GVarDecl(currVar, _ ) -> (currVar.vname = element_name)
                |   GVar(currVar, _, _ ) -> (currVar.vname = element_name)
                |   GFun(currFunc, _) -> (currFunc.svar.vname = element_name)
                |   GType(currType, _) -> (currType.tname = element_name)
                |   _ -> false

            in 

            (*  If element name exists in the file, then do not include the
             *  header file. Else do.
             * *)
            if List.exists element_exists currGlobals  then
                ()
            else
                needed_header_files := 
                    GText ("#include <" ^ header_file ^ ">") ::
                        !needed_header_files

        in
        begin

            (*  Repeat the process for every tuple in the list.
             * *)
            List.iter process_include_tuple header_file_tuples;
            !needed_header_files
        end
    
(*  The basic objective of this function is to bunch together all the special
 *  condition macros that need to inserted before the zcheck.h  file is included
 *  in the file being processed
 * *)
 let special_macros (is_main_file : bool) : global list =
        (*  Lets check for main file and include the required macro
         * *)
        let main_file_macro =
            if is_main_file then
                GText("#define GZ_MAIN_FILE 1")
            else
                (*  If this is not the main file, then just include a blank line    *)
                GText("")

        and miss_rate_macro = 
            if !instrMissRate then
                GText("#define GZ_INSTR_MISS_RATE 1")
            else
                (*  If this is not the main file, then just include a blank line    *)
                GText("")

        and isolate_checks_macro = 
            if !isolateChecks then
                if !slowChecksOnly then
                    GText("#define GZ_SLOW_CHECKS_ONLY 1")
                else
                    GText("#define GZ_FAST_CHECKS_ONLY 1")
            else
                (*  If this is not the main file, then just include a blank line    *)
                GText("")

        and call_impact_macro = 
            if !testCallImpact then
                GText("#define GZ_TEST_CALL_IMPACT 1")
            else
                (*  If this is not the main file, then just include a blank line    *)
                GText("")
        
        in
        [main_file_macro; miss_rate_macro; isolate_checks_macro; call_impact_macro]


(*
 * Function to verify command line arguments.
 *)
let verifyCommandLineArgs () : unit = 
   begin

     (* verify guard zone size setting *)
     if ((not (!minGZSize mod 8 = 0)) ||
        (not (!maxGZSize mod 8 = 0)) ||
        (not (!defaultGZSize mod 8 = 0)) ||
        (not (!frontGZSizeGlobal mod 8 = 0))) then
      raise (Incorrect_Input ("Guard zone sizes must be multiple of 8."));

     if (not (!minGZSize < !maxGZSize)) then
       raise (Incorrect_Input ("Minimum guard zone size must be less than maximum
       guard zone size."));

     if ((!defaultGZSize < !minGZSize) ||
         (!defaultGZSize > !maxGZSize)) then
       raise (Incorrect_Input ("Default guard zone size must be greater than or
       equal to minimum guard zone size, and must be less than or equal to
       maximum guard zone size."));

     if ((!frontGZSizeGlobal < !minGZSize) ||
         (!frontGZSizeGlobal > !maxGZSize)) then
       raise (Incorrect_Input ("Front guard zone for globals must be greater than or
       equal to minimum guard zone size, and must be less than or equal to
       maximum guard zone size."));

     (* Verify setting of some options. *)
     if ((not !dontUseCCuredAnalysis) &&
         (!doConservativeAnalysis)) then
       raise (Incorrect_Input ("CCured analysis and conservative analysis can
       not be performed simulteneously. To use conservative analysis, use
       --dontUseCCuredAnalysis --doConservativeAnalysis as arguments to cilly."))

    end

(*  ======================================================================== *)

let transform = function (f:file) ->
    let file_name = validate_name (f.fileName)

    (*  The global variable that holds the minimum value of the 
     *  guardzone size for LBC *)
    and min_zone_size = (makeGlobalVar "min_zone_size"
                    (TInt(IUInt,[])) )

    (*  The global variable that holds the maximum value of the 
     *  guardzone size for LBC *)
    and max_zone_size = (makeGlobalVar "max_zone_size"
                    (TInt(IUInt,[])) )

    and min_zone_size_value = Const(CInt64((Int64.of_int !minGZSize), IUInt,
                                None))

    and max_zone_size_value = Const(CInt64((Int64.of_int !maxGZSize), IUInt,
                                None))
    in

    let min_zone_size_init = { init = Some( SingleInit(min_zone_size_value) ) }

    and max_zone_size_init = { init = Some( SingleInit(max_zone_size_value) ) }

    in
    (*  Lets transform all variable types and references.
     *  Note that this object will handle both global variables and FUNCTIONS.
     * *)
    let globalTransformer = new transformationVisitor   f 
                                                file_name
    
    (*  The actual introduction of checks on pointer dereferences is done by
     *  the visitor below   *)
    and instrumenter = new instrVisitor f

    (*
     * Here we push the initialization of stack variables at the place where
     * it's address is actually taken.
     *
     * NOTE: This analysis is currently unused.
     *)
    (* and pushInitToPropPlace = new initPlacer f file_name *)

    (*
     * The visitor below creates 2 copies of each function.
     * In one copy, all formal pointer arguments are annotated as WILD i.e., Unsafe.
     * We don't do anything to another copy.
     *
     * The idea is, later on we transform function calls to use one of these 2
     * copies. While doing this, if all actual arguments are SAFE, we will use
     * 2nd version of function otherwise we will use first.
     *
     * This is based on finding that most of the formal pointer parameters of a
     * function are SAFE.
     *
     * NOTE: This analysis is currently unused.
     *)
    (*and transformFuncsSafeUnsafe = new transformFunctionsSafeUnsafe f
                                                file_name *)

    (*
     * This visitor visits every guardzone check, and checks if the pointer
     * dereferenced in the check is safe or unsafe. 
     *
     * If it is safe, then it removes the check. Otherwise it keeps the
     * check as it is
     *)
    and safeIsCharGuardCRemover = new remSafeIsCharGuardCVisitor f file_name

    (* 
     * Wild tag all the formal and global pointers of a function.
     *)
    and wildTagger = new wildTagFormalGlobalPointerVisitor f file_name

    (*
     * Replace call to instrumented memory allocation
     * by call to original (uninstrumented) memory allocation 
     * routine in case the return pointer is SAFE
     *)
    and memmgmtFuncsProcessor = new replaceMemallocToOrigForSafePtr f file_name

    (*
     * NOTE: The analyzes provided by these options is not used currently, but the code is
     * commented out just in case someone wants to use it later.
    (*
     * Transforming the functions by introducing new functions with modified
     * formal parameters is done by visitor below.
     *
     * e.g. void foo(int* bar) 
     *      is transformed into
     *      void foo(int* bar, unsigned int bar_lo, unsigned int bar_hi)
     *)
    and transformFuncs = new transformFunctions f
                                                file_name

    (* The introduction of bound variables for a local pointer is done by
     * the visitor below *)
    and bndsIntroductor = new boundsIntroductor f 
                                                file_name

    (* The introduction of assignments bound variables for a local pointer is done by
     * the visitor below *)
    and bndsTracker = new boundsTracker f file_name

    and eliminateGZC = new eliminateGZChecks f file_name *)

    (*  Now the heap operations, memory allocation routines have been moved
     *  into a library and hence there is no need for zcheck.c . The
     *  inclusion of zcheck.h will suffice. Hence there is no need to define
     *  the MAIN_FILE macro.    *)
    and inc_zcheck = GText ("#include <zcheck.h>") 

    (*  Here we generate a list of header files that are needed in zcheck.h and
     *  are NOT present in the current file.
     * *)
    and inc_headers = (include_files f.globals)

    in

    (*  This try-catch block exists so that in case of an error, we could
     *  properly terminate logging and then rethrow the error upwards.
     *  *)
    try (

        (* IMP: This is set in src/frontc/cabs2cil.ml *)
        Cabs2cil.doCollapseCallCast := true;

        (*  We use functions like Cil.sizeOf that needs this initialization to
         *  be done.
         *)
        (Cil.initCIL ());

        (* Let us verify command line arguments. *)
        verifyCommandLineArgs ();

        (*  Init logs   *)
        init_log f;

        (* 
         * For conservative mode analysis, we tag all the formal pointer
         * arguments of a function and global pointers as WILD.
         *
         * This mode is to be used for separate compilation only.
         *)
        if(!doConservativeAnalysis) then
         visitCilFile (wildTagger :> cilVisitor) f;

        (*
         * Do the CCured type inference analysis before
         * we introduce impurity to existing program by using
         * casting in is_char_guard.
         *)
        if (not !dontUseCCuredAnalysis) then
        begin
				  (*
				   * We first transform functions by creating 2 copies of each function.
				   * One copy has all the pointers annotated as WILD.
				   * This is used for conservative approach to analysis.
				   * The other copy has it's pointer kinds inferred by
				   * CCured analysis.
				   * Assumption is that CCured analysis will mark pointer kinds
				   * as SAFE which will help us gain performance by removing
				   * safe guardzone checks.
				   *
				   * NOTE: The analysis provided by this option is currently not used.
				   *)
				  (*visitCilFile (transformFuncsSafeUnsafe :> cilVisitor) f;*)

				  (*
				   * Use CCured pointer-kind inference to find out
				   * which pointers are safe and which are unsafe.
				   *)

				  (* initialize Type module of CCured *)
				   Type.init ();

				  (* remove unused temporaries *)
				   Rmtmps.removeUnusedTemps f;

				  (* Setting the flags needed for proper behavior of CCured the way we want. *)
				   Ptrnode.use_wild_solver := false;
				   Ptrnode.defaultIsWild := false;
				   Markptr.noStackOverflowChecks := true;
				   Ptrnode.allowInlineAssembly := true;
				   Ptrnode.extendStringBuffers := false;
				   Ptrnode.emitGraphDetailLevel := 3;
           Ptrnode.inferFile := None;

				  let infer = 
				    (* Collecting constraints *)
				    let marked = Markptr.markFile f in
				    (* Solve the graph *)
				    (* Solving constraints *)
				    (* invoking the solver *)
				    (Util.tryFinally
				     (fun _ ->
				      (fun graph ->
				       (*if (!maxSplit) then begin
				         Solver.markAllSplit := true;
				       end ;*)
				       (* Here we actually call the solver *)
				       let should_typecheck = 
				         if !Ptrnode.use_wild_solver then 
				           Solveutil.wild_solve graph 
				         else
				           Solver.solve marked graph
				       in 
				       should_typecheck
				       (*if should_typecheck && not !typecheck then begin 
				         ignore (E.warn "The inference results should be type-checked.")
				       end ; *)
				     ) Ptrnode.idNode
				    )
				    (* Now the finally clause *)
				    (fun _ ->
				      Ptrnode.printGraphStats ();
				      (match !Ptrnode.inferFile with
				        None -> ()
				        | Some f ->
				          (Ptrnode.printInfer f) marked);
				    )
            )
				  ();
				  marked 
				  in 
				  if !E.hadErrors then
				      (print_string "Marker had errors. Hence skipping CCured
				      analysis";)
				  else
				    begin
				      Typecheck.typecheck_file infer;
				    end 
		    end; (*end CCured analysis check *)

        (*  Setting the global variable symbols_list to the list that we
         *  have read in from the input file specified  *)
        symbols_list := read_file !symbolFile;
        (*  Setting the global variable sys_dirs_list to the list that we
         *  have read in from the input file specified  *)
        sys_dirs_list := read_file !sysDirsFile;
        (*  Setting the global variable functions_list to the hashtable that we
         *  have read in from the input file specified  *)
        read_functions_file !functionsFile;

         (* Setting the global variable iufunctions_list to the list that we
         * have read in from the input file specified. *)
        iufunctions_list := read_file !iuFunctionsFile;

        (*  We need to perform constant folding over the entire file. This is
         *  because in OpenSSL we came across declarations that involved sizeof
         *  expressions that cause problems.
         *  Running constantFolding over the entire file should alleviate this
         *  problem
         * *)
         visitCilFile (Cil.constFoldVisitor true) f;

        (*  Note that here we do not transform the variables themselves if we are to
         *  test the performance impact of only the guardzone checks without
         *  taking the memory effects of the transformation
         *  *)
        if (not !testInstr) then
         begin
             (* Initialize the hash table required to transform 
              * the use of memory management functions into their wrappers. *)
             initMemMgmtFuncsWrappersHT;
             visitCilFile (globalTransformer :> cilVisitor) f;
         end;

        let min_zone_size_var_def =
            if globalTransformer#is_main_file then
                GVar(min_zone_size, min_zone_size_init, locUnknown)
            else
                (*  If this is not the main file, then just include a blank line    *)
                GText("")
            
        and max_zone_size_var_def =
            if globalTransformer#is_main_file then
                GVar(max_zone_size, max_zone_size_init, locUnknown)
            else
                (*  If this is not the main file, then just include a blank line    *)
                GText("")

        and special_macro_list = special_macros (globalTransformer#is_main_file )
        
        in
          f.globals <- special_macro_list @  inc_headers @ 
          [inc_zcheck; min_zone_size_var_def; max_zone_size_var_def] @ 
                    f.globals;

        (*
         * Here we push the initialization of stack variables
         * at the place where it's address is first taken.
         *
         * NOTE: The analysis associated with this option is currently not used.
         *)
        (*if (not !testInitPush) then
          visitCilFile (pushInitToPropPlace :> cilVisitor) f;*)

        (*  Note that we do not instrument pointer dereferences if we are to
         *  test the performance impact of only the guardzone initialization
         *  routines.
         *)
        if (not !testInit) then
            visitCilFile (instrumenter :> cilVisitor) f;

        (*
         * We now use CCured results to optimize
         * away unnecessary zone checks or unnecessary
         * variable transformations.
         *)
        if (not !dontUseCCuredAnalysis) then
        begin
            
            (* Init the hash table required to replace memory
             * allocation function call.
             *)
            initMemMgmtFuncsHT;

            (*
             * Replace call to instrumented memory allocation
             * by call to original (uninstrumented) memory allocation 
             * routine in case the return pointer is SAFE
             *)
            visitCilFile (memmgmtFuncsProcessor :> cilVisitor) f;

            (*
             * Use CCured analysis result to find out which 
             * guard zone checks can be removed.
             *)
            visitCilFile (safeIsCharGuardCRemover :> cilVisitor) f;

            (* Print check kept & remove statistics *)
            (print_string "\n\n-----------------------------\n");
            (print_string "    Check Statistics        \n");
            (print_string "-----------------------------\n");
            (print_string ("TOTAL  : " ^ string_of_int(!total_checks)));
            (print_string ("\nREMOVE : " ^ string_of_int(!removed_checks)));
            (print_string ("\nKEPT   : " ^ string_of_int(!kept_checks)));
            (print_string "\n\n");
        end;

        (* Transform function definitions by making a new copy of 
         * function, changing it's name from old to old_bnd_trans,
         * and introducing low and high bounds for formal parameters 
         * which are pointers.
         *
         * NOTE: We don't use analysis provided by these options now, but the
         * code is kept just in case someone wants to work it later.
         * 
         * If dontIntroTrackBounds is set to true, then skip this step.
         *)
        (*if ((not !dontIntroTrackBounds) &&
            (not !dontDoInterProcBoundTracking)) then 
            visitCilFile (transformFuncs :> cilVisitor) f; 
        *)

        (* Introduce bound variables for local pointers i.e., pointers that are local to
         * functions. This transformation doesn't introduce bounds check itself.
         * This is done in next transformation.
         *
         * If dontIntroTrackBounds is set to true, then skip this step.
         *)
        (*if (not !dontIntroTrackBounds) then 
            visitCilFile (bndsIntroductor :> cilVisitor) f;*)

        (*
         * Track and introduce assignments to bounds of pointers
         * wherever assignment to pointer is done.
         *)
        (*if (not !dontIntroTrackBounds) then 
            visitCilFile (bndsTracker :> cilVisitor) f; *)

        (*if (not !dontEliminateGZChecks) then
            visitCilFile (eliminateGZC :> cilVisitor) f;*)
        
        ;

        (* Terminate logging   *)
        if (not !disableLogFileGeneration) then
          terminate_log f.fileName
    )
    with
    |   error -> 
            begin
                terminate_log f.fileName;
                raise error
            end

let feature : featureDescr = 
    {
        fd_name = "zcheck";
        fd_enabled = doZCheck;
        fd_description = "generation of code with instrumentation for sequential" ^
                         "\n\t\t\t\t buffer overflow protection using guard zones"; 
        fd_extraopt = [ ("--minGZSize", Arg.Set_int(minGZSize), 
                         " Set the minimum size of guardzone for LBC. Note that it " ^
                         "necessarily must be multiple of 8. ");

                         ("--maxGZSize", Arg.Set_int(maxGZSize),
                         " Set the maximum size of guardzone for LBC. Note that it " ^
                         "necessarily must be multiple of 8. ");

                         ("--defaultGZSize", Arg.Set_int(defaultGZSize),
                         " Set the default size of guardzone for LBC. This is " ^
                         "used in places where guard zone size could \n\t\t\t\tnot be " ^
                         "determined from the type of the variable because it has " ^
                         "incomplete type. Note that it\n\t\t\t\t" ^
                         "necessarily must be multiple of 8. ");

                        ("--symbolFile", Arg.Set_string(symbolFile), 
                        " Full name of the file that would contain the names of" ^
                        " global symbols (specifically" ^ 
                        "\n\t\t\t\t" ^
                        "variables) that must be excluded from transformation."  ^
                        " There must be ONLY one symbol name" ^ 
                        "\n\t\t\t\t" ^
                        "per line.");
                        
                        ("--sysDirsFile", Arg.Set_string(sysDirsFile), 
                        " Full name of the file that would contain the names of" ^
                        " system directories. Functions" ^ 
                        "\n\t\t\t\t" ^ 
                        "that belongs to files in these directories will not be" ^
                        " instrumented. There must be ONLY" ^
                        "\n\t\t\t\t" ^ 
                        "one directory name per line. Do not forget to include the ending \"/\".");
                        
                        ("--extendedChecks", Arg.Set(extendedCheck), 
                        " Ensure that entire variable is clean (not overlapping" ^
                        " guardzone) as compared to ensuring" ^ 
                        "\n\t\t\t\t" ^ "that the first byte is clean.");
                        
                        ("--testInitialization", Arg.Set(testInit), 
                        " Enables transformation of variables and references" ^
                        " without pointer dereference" ^
                        "\n\t\t\t\t" ^ 
                        "instrumentation. This helps to measure the performance" ^
                        " impact of ONLY initialization" ^
                        "\n\t\t\t\t" ^ "routines.");
                        
                        ("--testInstrumentation", Arg.Set(testInstr), 
                        " Enables only the instrumentation of pointer" ^
                        " dereferences without transformation of" ^
                        "\n\t\t\t\t" ^
                        "variables and references. This helps to measure the" ^
                        " performance impact of ONLY" ^
                        "\n\t\t\t\t" ^ 
                        "instrumentation without any memory effects.")

                        ;("--instrOnlyReads", Arg.Set(instrReadsOnly), 
                        " Adds instrumentation to only guardzone check pointer" ^
                        " dereferences that read data. The" ^
                        "\n\t\t\t\t" ^ "data-writes are NOT instrumented.")

                        ;("--instrMissRate", Arg.Set(instrMissRate), 
                        " Adds instrumentation that measures the number of" ^
                        " times the slow vs fast guardzone checks \n\t\t\t\tare called.")

                        ;("--isolateChecks", Arg.Set(isolateChecks), 
                        " This option helps separate fast checks from the" ^
                        " slow checks. Used for testing the" ^ 
                        "\n\t\t\t\t" ^
                        "performance impact of each type of check. By default," ^
                        " it's set to FALSE. If this switch is" ^
                        "\n\t\t\t\t" ^
                        "specified without --slowChecksOnly being specified," ^
                        " then only fast guardzone checks are" ^
                        "\n\t\t\t\t" ^ "performed.")

                        ;("--slowChecksOnly", Arg.Set(slowChecksOnly), 
                        " This switch works ONLY when --isolateChecks switch is" ^
                        " specified. With this switch" ^
                        "\n\t\t\t\t" ^
                        "fast-checks are disabled, and ONLY slow bitmap checks" ^
                        " are performed for every pointer" ^ 
                        "\n\t\t\t\t" ^
                        "dereference. This is to be used for TESTING PURPOSES ONLY.")

                        ;("--testCallImpact", Arg.Set(testCallImpact), 
                        " Used for testing the impact of mere presence of call" ^
                        " to slow checks. The slow check call" ^ 
                        "\n\t\t\t\t" ^ 
                        "is present but the function itself is NEVER called.")

                        ;("--functionsFile", Arg.Set_string(functionsFile), 
                        " Full name of the file that contains function names to" ^
                        " be EITHER exclusively instrumented or" ^
                        "\n\t\t\t\t" ^ 
                        "exclusively uninstrumented. The actions will be" ^
                        " dictated by --doNotInstrument." ^
                        "\n\t\t\t\t" ^ 
                        "The default value of this option is empty list.")

                        ;("--doInstrument", Arg.Set(doInstrument), 
                        " The option indicates that functions in the" ^
                        " --functionsFile will be exclusively" ^
                        "\n\t\t\t\t" ^ 
                        "instrumented. The default action is to exclusively NOT INSTRUMENT.")

                        ;("--dontTransformLocals", Arg.Set(dontTransformLocals), 
                        " This option applies MAINLY to the functions that will" ^
                        " NOT be instrumented in the exclusive" ^
                        "\n\t\t\t\t" ^
                        "instrumentation/non-instrumentation mode. This option" ^
                        " specifies NOT to transform the local" ^
                        "\n\t\t\t\t" ^
                        "variables if possible. The default is to transform the local variables.")

                        (*
                         * NOTE: We don't use the analysis provided by
                         * options below and hence commented.
                         *
                        ;("--dontIntroTrackBounds", Arg.Set(dontIntroTrackBounds),
                        " This option applies to functions and if set, won't" ^
                        "\n\t\t\t\t" ^ 
                        "introduce and track the bounds of a local pointer in functions.")

                        ;("--dontDoInterProcBoundTracking", Arg.Set(dontDoInterProcBoundTracking),
                        "This option disables inter-procedure bound tracking in" ^
                        "\n\t\t\t\t" ^
                        "which static functions are transformed if a formal argument" ^
                        "\n\t\t\t\t is of pointer type. The transformed function" ^
                        "\n\t\t\t\t has low and high bounds as additional" ^
                        "\n\t\t\t\t parameter. The call site is also modified.")

                        ;("--dontEliminateGZChecks",Arg.Set(dontEliminateGZChecks),
                        "This option disables elimination of guard-zone or bound" ^
                        "check done using reaching definition information")

                        *)

                        ;("--dontUseCCuredAnalysis",
                        Arg.Set(dontUseCCuredAnalysis),
                        " This option, if set, will disable the use of CCured type analysis " ^
                        " to get rid of \n\t\t\t\tunnecessary guardzone" ^
                        " checks. To use this option, one must use whole-program" ^
                        " analysis mode \n\t\t\t\tusing --merge option.")

                        ;("--doConservativeAnalysis",
                        Arg.Set(doConservativeAnalysis),
                        " This option if set, enables the conservative mode of" ^
                        " analysis in which, by default, \n\t\t\t\tpointer dereferences" ^
                        " are guardzone checked, unless, static analysis figures" ^
                        " out that \n\t\t\t\tthe pointer is used safely.")

                        ;("--disableLogFileGeneration",
                        Arg.Set(disableLogFileGeneration),
                        " This option disables logging which is needed for successful" ^
                        " merge mode compilation of \n\t\t\t\tsome large packages.")

                        (* NOTE: This option is currently not used.
                        ;("--test-initpush", Arg.Set(testInitPush), "")
                        *)
                        ;("--inituninitFuncFile", Arg.Set_string(iuFunctionsFile),
                          " This option contains a full path of the file which" ^
                          " contains the list of functions \n\t\t\t\tto be excluded" ^
                          " from initialization and uninitialization.")
        ];
        fd_doit = transform;
        fd_post_check = true;
    }

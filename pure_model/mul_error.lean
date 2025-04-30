
import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
import LeanRV64DLEAN


open Functions
open Retired
open Sail


/- MUL function from the SailLean modell

def execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) : SailM Retired := do
  let rs1_val ← do (rX_bits rs1)
  let rs2_val ← do (rX_bits rs2)
  let rs1_int : Int :=
    if mul_op.signed_rs1
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if mul_op.signed_rs2
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let result_wide := (to_bits (2 *i xlen) (rs1_int *i rs2_int))
  let result :=
    if mul_op.high
    then (Sail.BitVec.extractLsb result_wide ((2 *i xlen) -i 1) xlen)
    else (Sail.BitVec.extractLsb result_wide (xlen -i 1) 0)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)
-/

/-


/-- Type quantifiers: n : Int, l : Nat, l ≥ 0 -/
def to_bits (l : Nat) (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)


def get_slice_int (len lo : Nat) (n : Int) : BitVec len :=
  BitVec.extractLsb' lo len (BitVec.ofInt (lo + len + 1) n)

def to_bits (l : Nat) (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)


-- Sail version
def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb hi lo

-/
def get_slice_int1 (len lo : Nat) (n : Int) : BitVec len :=
  BitVec.extractLsb' lo len (BitVec.ofInt (lo + len + 1) n)


def execute_MUL_pure64 (mul_op : mul_op) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_int : Int :=
    if mul_op.signed_rs1 -- if signed then modell as integer operation
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
    --dbg_trace " hello {rs1_val.toInt}"
  let rs2_int : Int :=
    if mul_op.signed_rs2
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  dbg_trace " START  {rs1_int} {rs2_int} {rs1_int *i rs2_int }"
  let result_wide := (get_slice_int1 (2 *i Functions.xlen) 0 (rs1_int *i rs2_int) ) --adapt result vector width to 2^(exp1 + exp2)
  dbg_trace " AFTER {result_wide}"
  dbg_trace " len {2 *i Functions.xlen}"
  let result :=
    if mul_op.high -- if set return the higher xlen bits else the lower
    then (Sail.BitVec.extractLsb result_wide ((2 *i Functions.xlen) -i 1) Functions.xlen) --return either higher or lower xlen bits
    else (Sail.BitVec.extractLsb result_wide (Functions.xlen -i 1) 0)
  result

def skeleton_binary  (rs2 : regidx) (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := execute_func rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS


theorem mul_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_MUL_pure64 mul_op val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary execute_MUL_pure64
  rfl



def x := BitVec.ofInt 64 (-1)

/- this file was for debugging the riscv semantics of the saillean modell -/
#eval  execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= False, signed_rs2 := False }) (10#64) (9#64)

#eval  execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= True, signed_rs2 := False }) (100#64) (x)


example : execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= False, signed_rs2 := False }) (1#64) (1#64)
  = 1#64 := rfl


#eval  execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= False, signed_rs2 := False }) (9#64) (99#64)



/-
example :
  let mul_op := { high := False, signed_rs1:= False, signed_rs2 := False }
  let state := sorry
  let r0 := regidx.Regidx 0#5
  Functions.execute_MUL r0 r0 r0 mul_op state
  = ...
-/


import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
import LeanRV64DLEAN


set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Functions
open Retired
open Sail


--14 functions

 /- def execute_ADDIW (imm : (BitVec 12)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) : SailM Retired := do
  let result ← do (pure ((← (Functions.rX_bits rs1)) + (sign_extend (m := ((2 ^i 3) *i 8)) imm)))
  (wX_bits rd (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb result 31 0)))
  (pure RETIRE_SUCCESS) -/
namespace PureFunctions
--purified
-- semantics: adds signed extended immediate to reg rs1 and prodcues sign-extension of 64 bit result in result register
def execute_ADDIW_pure64 (imm : (BitVec 12)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let result :=  rs1_val + (sign_extend (m := ((2 ^i 3) *i 8)) imm) -- rs1_val + sign extended immediate
  (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb result 31 0))

/-
def execute_UTYPE (imm : (BitVec 20)) (rd : (BitVec 5)) (op : uop) : SailM Retired := do
  let off : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) (imm ++ (0x000 : (BitVec 12))))
  (wX_bits rd
    (← do
      match op with
      | RISCV_LUI => (pure off)
      | RISCV_AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)
-/
-- TO DO: build diffrent skeletion for it
--purified, utype means upper immediate type, used for loading large constants and efficientl working with them
-- careful: modelled the program counter as an extra input

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM Retired := do
  let off : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) (imm ++ (0x000 : (BitVec 12))))
  (wX_bits rd
    (← do
      match op with
      | uop.RISCV_LUI => (pure off)
      | uop.RISCV_AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)


def execute_UTYPE_pure64 (imm : (BitVec 20)) (pc : (BitVec 64)) (op : uop)  : BitVec 64 :=
  let off : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) (imm ++ (0x000 : (BitVec 12)))) --loads immediate into upper 20 bits and then fills the rest up with 0
  let result := match op with
      | uop.RISCV_LUI => off
      | uop.RISCV_AUIPC => BitVec.add off pc
  result
/-
def execute_SHIFTIWOP (shamt : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (op : sopw) : SailM Retired := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | RISCV_SLLIW => (shift_bits_left rs1_val shamt)
    | RISCV_SRLIW => (shift_bits_right rs1_val shamt)
    | RISCV_SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := ((2 ^i 3) *i 8)) result))
  (pure RETIRE_SUCCESS)
  -/
-- TO DO: need an own skelecton
-- purified
def execute_SHIFTIWOP_pure64 (shamt : (BitVec 5)) (op : sopw) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb (rs1_val) 31 0
  let result : (BitVec 32) :=
    match op with
    | sopw.RISCV_SLLIW => (shift_bits_left rs1_val32 shamt)
    | sopw.RISCV_SRLIW => (shift_bits_right rs1_val32 shamt)
    | sopw.RISCV_SRAIW => (shift_bits_right_arith rs1_val32 shamt)
  (sign_extend (m := ((2 ^i 3) *i 8)) result) -- sign extend it to 64 bit again

/-
def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (op : sop) : SailM Retired := do
  (wX_bits rd
    (← do
      match op with
      | RISCV_SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | RISCV_SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | RISCV_SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)
  -/

-- TO DO: need an extra skeleton
-- purified
def execute_SHIFTIOP_pure64 (shamt : (BitVec 6)) (op : sop) (rs1_val : (BitVec 64)) : BitVec 64 :=
      match op with
      | sop.RISCV_SLLI => (shift_bits_left rs1_val shamt)
      | sop.RISCV_SRLI => (shift_bits_right rs1_val shamt)
      | sop.RISCV_SRAI => (shift_bits_right_arith (rs1_val) shamt)

/-
def execute_RTYPEW (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (op : ropw) : SailM Retired := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | RISCV_ADDW => (rs1_val + rs2_val)
    | RISCV_SUBW => (rs1_val - rs2_val)
    | RISCV_SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | RISCV_SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | RISCV_SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := ((2 ^i 3) *i 8)) result))
  (pure RETIRE_SUCCESS)
-/
-- purified, *W suffix indicates that operates on the lower 32 bits, done
def execute_RTYPEW_pure64 (op : ropw) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let rs2_val32 :=  Sail.BitVec.extractLsb rs2_val 31 0
  let result : (BitVec 32) :=
    match op with
    | ropw.RISCV_ADDW => (rs1_val32 + rs2_val32)
    | ropw.RISCV_SUBW => (rs1_val32 - rs2_val32)
    | ropw.RISCV_SLLW => (shift_bits_left rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
    | ropw.RISCV_SRLW => (shift_bits_right rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
    | ropw.RISCV_SRAW => (shift_bits_right_arith rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
  ((sign_extend (m := ((2 ^i 3) *i 8)) result)) -- sign extended the result to 64 bits again


/-
def execute_RTYPE (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (op : rop) : SailM Retired := do
  (wX_bits rd
    (← do
      match op with
      | RISCV_ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | RISCV_SLT =>
        (pure (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | RISCV_SLTU =>
        (pure (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | RISCV_AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | RISCV_OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | RISCV_XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | RISCV_SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | RISCV_SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | RISCV_SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | RISCV_SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)
-/
/- def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM Retired := do
  (wX_bits rd
    (← do
      match op with
      | RISCV_ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | RISCV_SLT =>
        (pure (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | RISCV_SLTU =>
        (pure (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | RISCV_AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | RISCV_OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | RISCV_XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | RISCV_SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | RISCV_SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | RISCV_SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | RISCV_SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS) -/

-- purified,
def execute_RTYPE_pure64 (op : rop)  (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)): BitVec 64 :=
  let result :=
      match op with
      | rop.RISCV_ADD => rs2_val + rs1_val
      | rop.RISCV_SLT =>
        (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_s (rs1_val) (rs2_val)))) -- checks that lhs is less than rhs and set the bool accordingly
      | rop.RISCV_SLTU =>
         (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_u (rs1_val) (rs2_val))))
      | rop.RISCV_AND => rs1_val &&& rs2_val
      | rop.RISCV_OR => rs1_val ||| rs2_val
      | rop.RISCV_XOR => rs1_val ^^^ rs2_val
      | rop.RISCV_SLL =>
        (shift_bits_left (rs1_val) --reason for log2.. etc is it extracts the lower 6 bits where the shift command is encoded
            (Sail.BitVec.extractLsb (rs2_val) (Functions.log2_xlen -i 1) 0)) --(log2_xlen -i 1) log2_xlen yields 6 thus overall extracts the last 5 bits
      | rop.RISCV_SRL =>
        (shift_bits_right (rs1_val)
            (Sail.BitVec.extractLsb (rs2_val) (Functions.log2_xlen -i 1) 0))
      | rop.RISCV_SUB => rs1_val - rs2_val
      | rop.RISCV_SRA =>
        (shift_bits_right_arith (rs1_val)
            (Sail.BitVec.extractLsb (rs2_val) (Functions.log2_xlen -i 1) 0))
      result

/-
/-- Type quantifiers: k_ex287536# : Bool -/
def execute_REMW (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (s : Bool) : SailM Retired := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let r : Int :=
    if (BEq.beq rs2_int 0)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (sign_extend (m := ((2 ^i 3) *i 8)) (to_bits 32 r)))
  (pure RETIRE_SUCCESS)
-/

--purified
def execute_REMW_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)): BitVec 64 :=
  let rs1_val32 :=  (Sail.BitVec.extractLsb (rs1_val) 31 0)
  let rs2_val32 :=  (Sail.BitVec.extractLsb (rs2_val) 31 0)
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val32)
    else (BitVec.toNat rs1_val32)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val32)
    else (BitVec.toNat rs2_val32)
  let r : Int :=
    if (BEq.beq rs2_int 0)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  sign_extend (m := ((2 ^i 3) *i 8)) (to_bits 32 r) -- convert it to 32 bits and then sign extend it to 64
/-
/-- Type quantifiers: k_ex287551# : Bool -/
def execute_REM (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (s : Bool) : SailM Retired := do
  let rs1_val ← do (rX_bits rs1)
  let rs2_val ← do (rX_bits rs2)
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let r : Int :=
    if (BEq.beq rs2_int 0)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (to_bits xlen r))
  (pure RETIRE_SUCCESS)
-/
--purified
def execute_REM_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_int : Int :=
    if s -- checks sign
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let r : Int :=
    if (BEq.beq rs2_int 0) --checks if  mod zero or not
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (to_bits Functions.xlen r) -- converts it to xlen bits, usually 64



/-
def execute_MULW (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) : SailM Retired := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int : Int := (BitVec.toInt rs1_val)
  let rs2_int : Int := (BitVec.toInt rs2_val)
  let result32 := (Sail.BitVec.extractLsb (to_bits 64 (rs1_int *i rs2_int)) 31 0)
  let result : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) result32)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)
-/

--purified
-- computes product of the 32 lower bits of each reg then sign extends it to 64 bits
def execute_MULW_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := (Sail.BitVec.extractLsb rs1_val 31 0)
  let rs2_val32 := (Sail.BitVec.extractLsb rs2_val 31 0)
  let rs1_int : Int := (BitVec.toInt rs1_val32)
  let rs2_int : Int := (BitVec.toInt rs2_val32)
  let result32 := (Sail.BitVec.extractLsb (to_bits 64 (rs1_int *i rs2_int)) 31 0)
  let result : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) result32)
  result
/-
def execute_MUL (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (mul_op : mul_op) : SailM Retired := do
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
--purified, done
def execute_MUL_pure64 (mul_op : mul_op) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_int : Int :=
    if mul_op.signed_rs1 -- if signed then modell as integer operation
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if mul_op.signed_rs2
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let result_wide := (to_bits (2 *i Functions.xlen) (rs1_int *i rs2_int)) --adapt result vector width to 2^(exp1 + exp2)
  let result :=
    if mul_op.high -- if set return the higher xlen bits else the lower
    then (Sail.BitVec.extractLsb result_wide ((2 *i Functions.xlen) -i 1) Functions.xlen) --return either higher or lower xlen bits
    else (Sail.BitVec.extractLsb result_wide (Functions.xlen -i 1) 0)
  result
/-
def execute_DIVW (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (s : Bool) : SailM Retired := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let q : Int :=
    if (BEq.beq rs2_int 0)
    then (-1)
    else (Int.tdiv rs1_int rs2_int)
  let q' : Int :=
    if (Bool.and s (q >b ((2 ^i 31) -i 1)))
    then (0 -i (2 ^i 31))
    else q
  (wX_bits rd (sign_extend (m := ((2 ^i 3) *i 8)) (to_bits 32 q')))
  (pure RETIRE_SUCCESS) -/

-- purified
def execute_DIVW_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb (rs1_val) 31 0
  let rs2_val32 :=  Sail.BitVec.extractLsb (rs2_val) 31 0
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val32)
    else (BitVec.toNat rs1_val32)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val32)
    else (BitVec.toNat rs2_val32)
  let q : Int :=
    if (BEq.beq rs2_int 0)
    then (-1)
    else (Int.tdiv rs1_int rs2_int)
  let q' : Int :=
    if (Bool.and s (q >b ((2 ^i 31) -i 1)))
    then (0 -i (2 ^i 31))
    else q
  sign_extend (m := ((2 ^i 3) *i 8)) (to_bits 32 q')

/-- Type quantifiers: k_ex290550# : Bool -/
/-
def execute_DIV (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (s : Bool) : SailM Retired := do
  let rs1_val ← do (rX_bits rs1)
  let rs2_val ← do (rX_bits rs2)
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let q : Int :=
    if (BEq.beq rs2_int 0)
    then (-1)
    else (Int.tdiv rs1_int rs2_int)
  let q' : Int :=
    if (Bool.and s (q >b xlen_max_signed))
    then xlen_min_signed
    else q
  (wX_bits rd (to_bits xlen q'))
  (pure RETIRE_SUCCESS)
-/
--purified
-- divisio of r1 by r2
def execute_DIV_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_int : Int :=
    if s -- checks if signed division or not
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let q : Int :=
    if (BEq.beq rs2_int 0) --checks wether its division by zero
    then (-1) -- no exception on division by zero, ATTENTION !
    else (Int.tdiv rs1_int rs2_int)
  let q' : Int :=
    if (Bool.and s (q >b xlen_max_signed)) -- in the overflow case we clamp the result to min_signed value
    then xlen_min_signed -- on overflow return smallest value but no exception ! ATTENTION
    else q
  (to_bits Functions.xlen q') -- return value

/-
def execute_ITYPE (imm : (BitVec 12)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (op : iop) : SailM Retired := do
  let immext : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) imm)
  (wX_bits rd
    (← do
      match op with
      | RISCV_ADDI => (pure ((← (rX_bits rs1)) + immext))
      | RISCV_SLTI =>
        (pure (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) immext))))
      | RISCV_SLTIU =>
        (pure (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) immext))))
      | RISCV_ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | RISCV_ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | RISCV_XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)
-/

--purified immediate operations, did let the immediate be 12 bit vector
def execute_ITYPE_pure64 (imm : (BitVec 12)) (rs1_val : (BitVec 64)) (op : iop) : BitVec 64 :=
   let immext : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) imm) -- sign extend immediate to 64 bits
    match op with -- result value will be returned instead of written into destination register
      | iop.RISCV_ADDI => rs1_val + immext --immediate addition
      | iop.RISCV_SLTI =>
        zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_s rs1_val immext)) --checks if immediate is strictly less than rs1_val and returns boolean as 64 bit sign extended result
      | iop.RISCV_SLTIU =>
         zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_u rs1_val immext))
      | iop.RISCV_ANDI =>  rs1_val &&& immext
      | iop.RISCV_ORI => rs1_val ||| immext
      | iop.RISCV_XORI => rs1_val ^^^ immext


/-
def execute_ZICOND_RTYPE (arg0 : (BitVec 5)) (arg1 : (BitVec 5)) (arg2 : (BitVec 5)) (arg3 : zicondop) : SailM Retired := do
  let merge_var := (arg0, arg1, arg2, arg3)
  match merge_var with
  | (rs2, rs1, rd, RISCV_CZERO_EQZ) =>
    let value ← do (rX_bits rs1)
    let condition ← do (rX_bits rs2)
    let result : xlenbits :=
      if (BEq.beq condition (zeros_implicit (n := ((2 ^i 3) *i 8))))
      then (zeros_implicit (n := ((2 ^i 3) *i 8)))
      else value
    (wX_bits rd result)
    (pure RETIRE_SUCCESS)
  | (rs2, rs1, rd, RISCV_CZERO_NEZ) =>
    let value ← do (rX_bits rs1)
    let condition ← do (rX_bits rs2)
    let result : xlenbits :=
      if (bne condition (zeros_implicit (n := ((2 ^i 3) *i 8))))
      then (zeros_implicit (n := ((2 ^i 3) *i 8)))
      else value
    (wX_bits rd result)
    (pure RETIRE_SUCCESS)
-/
-- purified
-- to do: ask if its valid to just match on op only and assume valid regs
def execute_ZICOND_RTYPE_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) (arg3 : zicondop) : BitVec 64 :=
  let merge_var := (rs2_val, rs1_val, arg3) -- original matches on reg number, we assuem valid register and match just on operation
  match merge_var with
  | (_, _, zicondop.RISCV_CZERO_EQZ) =>
    let value := rs1_val
    let condition := rs2_val
    let result : xlenbits :=
      if (BEq.beq condition (zeros_implicit (n := ((2 ^i 3) *i 8))))
      then (zeros_implicit (n := ((2 ^i 3) *i 8)))
      else value
    result
  | (_, _, zicondop.RISCV_CZERO_NEZ) =>
    let value := rs1_val
    let condition :=  rs2_val
    let result : xlenbits := -- xlenbits is a 64 bit vector
      if (bne condition (zeros_implicit (n := ((2 ^i 3) *i 8))))
      then (zeros_implicit (n := ((2 ^i 3) *i 8)))
      else value
    result
-- ZBA speeds up address transaltion and indexing into an array while ZBA is for basic bit manipulation
--ZBA speeds up pointer arithemtic while ZBB basic bit manipulation         
/-
def execute_ZBB_RTYPEW (rs2 : (BitVec 5)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (op : bropw_zbb) : SailM Retired := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let shamt ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 4 0))
  let result : (BitVec 32) :=
    match op with
    | RISCV_ROLW => (rotate_bits_left rs1_val shamt)
    | RISCV_RORW => (rotate_bits_right rs1_val shamt)
  (wX_bits rd (sign_extend (m := ((2 ^i 3) *i 8)) result)) -- ^is a macro power -> sign extends to 64 bits
  (pure RETIRE_SUCCESS)
-/
-- assuming 64 bit result vector

--def execute_ZBS_RTYPE
--def execute_ZBS_IOP
--def execute_ZBKB_RTYPE
--def execute_ZBKB_PACKW

def execute_ZBB_RTYPEW_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) (op : bropw_zbb) : BitVec 64 :=
  let shamt := Sail.BitVec.extractLsb (rs2_val) 4 0
  let result : (BitVec 32) :=
    match op with
    | bropw_zbb.RISCV_ROLW => (rotate_bits_left rs1_val shamt)
    | bropw_zbb.RISCV_RORW => (rotate_bits_right rs1_val shamt)
  sign_extend (m := ((2 ^i 3) *i 8)) result

--def execute_ZBB_RTYPE
--def execute_ZBB_EXTOP
--def execute_ZBA_RTYPEUW
--def execute_ZBA_RTYPE
end PureFunctions

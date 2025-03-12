import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
-- added the imports bellow, had to move pure_func to the library folder
import LeanRV64DLEAN
import LeanRV64DLEAN.pure_func


open Functions
open Retired
open Sail
open PureFunctions

--example execute_MUL rs2 rs1 rd mul_op  = skeleton2 rs2 rs1 (fun val1 val2 => execute_MUL_pure val1 val2 mulop ) := by

  /- def skeleton (rs2 : BitVec 5) (rs1 : BitVec 5) (rd : BitVec 5) (op : BitVec 32 → BitVec 32 → BitVec 32) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := op rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS -/


 -- regidx is of type BitVec
def skeleton_binary  (rs2 : regidx) (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := execute_func rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_unary (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let result := execute_func rs1_val
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_UTYPE (imm : BitVec 20) (rd : regidx) (op : uop) (execute_func : BitVec 20 → BitVec 64 → uop → BitVec 64) : SailM Retired := do
  let pc ← get_arch_pc () -- TO DO READ IN THE PC , think of the effects
  let result := execute_func imm pc op
  wX_bits rd result
  pure RETIRE_SUCCESS


theorem add_eq (Imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ADDIW (imm) (rs1) (rd) = skeleton_unary rs1 rd (execute_ADDIW_pure64 imm) := by
  unfold Functions.execute_ADDIW
  unfold skeleton_unary
  unfold execute_ADDIW_pure64
  simp

theorem utype_eq (imm : (BitVec 20)) (rd : regidx) (op : uop) :
    Functions.execute_UTYPE imm rd op = skeleton_UTYPE imm rd op (execute_UTYPE_pure64) := by
  sorry

theorem shiftiwop_eq (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) :
    Functions.execute_SHIFTIWOP (shamt) (rs1) (rd) (op) = skeleton_unary rs1 rd (fun val1 => PureFunctions.execute_SHIFTIWOP_pure64 shamt op val1) := by
  sorry

theorem shiftiop_eq (shamt : (BitVec 6)) (op : sop) (rs1 : regidx) (rd : regidx) :
    Functions.execute_SHIFTIOP (shamt) (rs1) (rd) (op) = skeleton_unary rs1 rd (fun val1 => execute_SHIFTIOP_pure64 shamt op val1)  := by
  sorry

theorem rtypew_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) :
    Functions.execute_RTYPEW (rs2) (rs1) (rd) (op) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_RTYPEW_pure64 op val2 val1) := by -- attention_ ordering of arguements
  sorry

theorem rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : (regidx)) (op : rop) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (op) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_RTYPE_pure64 op val2 val1) := by
  sorry

theorem remw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_REMW (rs2) (rs1) (rd) (s) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_REMW_pure64 s val2 val1) := by
  sorry

theorem rem_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_REM (rs2) (rs1) (rd) (s) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_REM_pure64 s val2 val1) := by
  sorry

theorem mulw_eq (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :
    Functions.execute_MULW (rs2) (rs1) (rd) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_MULW_pure64 val2 val1) := by
  sorry

theorem mul_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_MUL_pure64 mul_op val2 val1) := by
  sorry

theorem divw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_DIVW (rs2 ) (rs1) (rd) (s) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_DIVW_pure64 s val2 val1) := by
  sorry

theorem div_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_DIV (rs2) (rs1) (rd) (s) = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_DIV_pure64 s val2 val1) := by
  sorry

theorem itype_eq (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (op) = skeleton_unary rs1 rd (fun val1 => execute_ITYPE_pure64 imm val1 op) := by
  sorry

--theorem zicond_rtype_eq (arg0 : (BitVec 5)) (arg1 : (BitVec 5)) (arg2 : (BitVec 5)) (arg3 : zicondop) := by


-- TO DO ZICOND and ZBB RytPEW




--example proof attempt
/-example :
  execute_ZBB_RTYPEW rs2 rs1 rd op = skeleton rs2 rs1 rd (execute_ZBB_RTYPEW_pure32):= by
  sorry --[TO DO ]

from pairing with alex
--theorem rX_bits_eq (rX : BitVec 5) : rX_bits rX = regval_from_reg <$> _ := by -- (readReg <| Register.ofBitVec rX) := by
  --simp [rX_bits, Functions.rX]


example execute_MUL rs2 rs1 rd mul_op  = skeleton2 rs2 rs1 (fun val1 val2 => execute_MUL_pure val1 val2 mulop ) := by
  sorry

example executeADD rs2 rs1 rd addOP = skeleton2 rs2 rs1 (λ val1 val2 . executeAddPure val1 val2 addOp)

-/

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
 -- ZBS extension is extension for single-bit operations
 /-
extension to efficently work with single bits
bclr clear a specifc bit
bext -> extracts a specfic bit
binv -> inverts a specfic bit
bset -> sets a specifc bit

 -/
 theorem execute_ZBS_RTYPE_pure64_RISCV_BCLR (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BCLR
      = BitVec.and rs1_val (~~~(BitVec.zeroExtend 64 1#1 <<< BitVec.extractLsb  5 0 rs2_val))
  := by
  rfl

theorem execute_ZBS_RTYPE_pure64_RISCV_BEXT (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BEXT
      = BitVec.setWidth 64
    (match
      BitVec.and rs1_val (BitVec.setWidth 64 1#1 <<< BitVec.extractLsb 5 0 rs2_val) !=
        0#64 with
    | true => 1#1
    | false => 0#1) := by rfl

-- inverts the bit at the index given by the least signficant 6 bits in rs2_val
theorem execute_ZBS_RTYPE_pure64 (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BINV
      = BitVec.xor rs1_val  (BitVec.zeroExtend 64 1#1 <<< BitVec.extractLsb 5 0 rs2_val) := by rfl

-- tried to proof using bv_decide ASK WHY BV_DECIDE DOESNT SUCCED IN THIS PROOF
theorem execute_ZBS_RTYPE_pure64_bvD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BINV
      = BitVec.xor rs1_val  (BitVec.zeroExtend 64 1#1 <<< BitVec.extractLsb 5 0 rs2_val)
  := by
  unfold PureFunctions.execute_ZBS_RTYPE_pure64
  simp
  unfold shift_bits_left Sail.BitVec.extractLsb zero_extend Sail.BitVec.zeroExtend HPow.hPow instHPowInt_leanRV64DLEAN
  simp only [Int.reduceToNat, Int.reducePow, Int.reduceMul]
   -- when I do this I only get simplifications using bitvec and nat operations
  simp only [BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth, BitVec.shiftLeft_eq', Nat.sub_zero
    , Nat.reduceAdd, BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow]

theorem execute_ZBS_RTYPE_pure64_RISCV_BSET (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BSET
      = rs1_val ||| BitVec.zeroExtend 64 1#1 <<< BitVec.extractLsb 5 0 rs2_val
  := by
  unfold PureFunctions.execute_ZBS_RTYPE_pure64
  simp
  unfold Sail.BitVec.extractLsb shift_bits_left zero_extend Sail.BitVec.zeroExtend
  simp only [BitVec.truncate_eq_setWidth, BitVec.shiftLeft_eq', Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow]
  unfold HPow.hPow instHPowInt_leanRV64DLEAN
  bv_decide
  --rfl, works by using either bv_decide or rfl
  --bv_decide

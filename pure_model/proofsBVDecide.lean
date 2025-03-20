import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
import LeanRV64DLEAN
import LeanRV64DLEAN.pure_func
open Functions
open Retired
open Sail
open PureFunctions


theorem name (params₁ : type₁ ) (params₂ : type₂ ) (params₃ : type₃ ) :
  _ = _  := by sorry
  /- PROOF -/

-- COLLECTION OF PROOFS THAT CAN BE DONE WITH BV_DECIDE VERY SMOOTHLY AND NOT WITH RFL ETC.
--1. using Bv_decide
theorem execute_RTYPE_pure64__RISCV_AND (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPE_pure64 rop.RISCV_AND rs2_val rs1_val
    = BitVec.and rs1_val rs2_val := by
  unfold PureFunctions.execute_RTYPE_pure64
  bv_decide

-- 1. no possible by rfl etc
theorem execute_RTYPE_pure64__RISCV_AND1 (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPE_pure64 rop.RISCV_AND rs2_val rs1_val
    = BitVec.and rs1_val rs2_val := by
  unfold PureFunctions.execute_RTYPE_pure64
  rfl



-- COLLECTION OF PROOFS WHERE I DONT KNOW WHY THEY DON'T GET ACCEPTED BY BV_DECIDE

-- inverts the bit at the index given by the least signficant 6 bits in rs2_val
theorem execute_ZBS_RTYPE_pure64 (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BINV
      = BitVec.xor rs1_val  (BitVec.zeroExtend 64 1#1 <<< BitVec.extractLsb 5 0 rs2_val) := by rfl

-- ASK WHY BV_DECIDE DOESNT SUCCED IN THIS PROOF
-- tried to proof using bv_decide
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

-- ASK WHY BV_decide suceeds here but not above
theorem execute_ZBS_RTYPE_pure64_RISCV_BSET (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BSET
      = rs1_val ||| BitVec.zeroExtend 64 1#1 <<< BitVec.extractLsb 5 0 rs2_val
  := by
  unfold PureFunctions.execute_ZBS_RTYPE_pure64
  simp
  unfold Sail.BitVec.extractLsb shift_bits_left zero_extend Sail.BitVec.zeroExtend
  simp only [BitVec.truncate_eq_setWidth, BitVec.shiftLeft_eq', Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow]
  unfold HPow.hPow instHPowInt_leanRV64DLEAN -- to conclude the proof can either use bv_decide or rfl, both work but not sure why
  --simp only [Int.reduceToNat, Int.reducePow, Int.reduceMul, BitVec.reduceSetWidth] these are the steps done by simp and I taught bv_decide only works with ints
  bv_decide

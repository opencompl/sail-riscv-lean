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

/-!
## Content
This file contains some proofs and first intial attempts. G oal was to gain intuition for the Sail-RISCV modell and 
-/

-- 1. ugly
theorem execute_RTYPE_pure64__RISCV_SLTU (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 (rop.RISCV_SLTU) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) =
      let b := BitVec.ult rs1_val rs2_val;
      BitVec.setWidth 64 (BitVec.ofBool b)  := by
  unfold PureFunctions.execute_RTYPE_pure64
  simp
  unfold zero_extend Sail.BitVec.zeroExtend bool_to_bits bool_bits_forwards zopz0zI_u
  rfl

-- 1. nice rewrite
  theorem execute_RTYPE_pure64__RISCV_SLTU1 (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 (rop.RISCV_SLTU) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) =
      let b := BitVec.ult rs1_val rs2_val;
      BitVec.setWidth 64 (BitVec.ofBool b)  := by rfl

--2. longer proof before having the instance simp lemma that rewrote the instances
theorem execute_ITYPE_pure64_RISCV_ADDI (imm : BitVec 12) (rs1_val : BitVec 64) : PureFunctions.execute_ITYPE_pure64 imm rs1_val iop.RISCV_ADDI
    = let immext : BitVec 64 := (BitVec.signExtend (((2 ^ 3) * 8)) imm) ;
    BitVec.add rs1_val immext := by
unfold PureFunctions.execute_ITYPE_pure64
simp
unfold sign_extend Sail.BitVec.signExtend HPow.hPow instHPowInt_leanRV64DLEAN
bv_decide


--2 after having the simp lemma

@[simp] theorem sail_hPow_eq (x y : Int) : x ^ y  = x ^ y.toNat := by rfl

theorem execute_ITYPE_pure64_RISCV_ADDI1 (imm : BitVec 12) (rs1_val : BitVec 64) : PureFunctions.execute_ITYPE_pure64 imm rs1_val iop.RISCV_ADDI
    = let immext : BitVec 64 := (BitVec.signExtend (((2 ^ 3) * 8)) imm) ;
    BitVec.add rs1_val immext := by
unfold PureFunctions.execute_ITYPE_pure64
simp
unfold sign_extend Sail.BitVec.signExtend --HPow.hPow instHPowInt_leanRV64DLEAN
bv_decide

--3 proof where we need to unfold to use bv_decide while rfl directly sees it
theorem execute_ITYPE_pure64_RISCV_ANDI_bv (imm : BitVec 12) (rs1_val : BitVec 64) :
    PureFunctions.execute_ITYPE_pure64 imm rs1_val  iop.RISCV_ANDI
      = let immext : BitVec 64 := (BitVec.signExtend (((2 ^ 3) * 8)) imm);
      BitVec.and rs1_val immext := by
        unfold PureFunctions.execute_ITYPE_pure64
        simp
        unfold sign_extend Sail.BitVec.signExtend  HAnd.hAnd instHAndBitVec_leanRV64DLEAN instHAndOfAndOp
        bv_decide
    -- vs rfl directly can be applied -> generalizes to all logical bit vec operations
  theorem execute_ITYPE_pure64_RISCV_ANDI_rfl (imm : BitVec 12) (rs1_val : BitVec 64) :
    PureFunctions.execute_ITYPE_pure64 imm rs1_val  iop.RISCV_ANDI
      = let immext : BitVec 64 := (BitVec.signExtend (((2 ^ 3) * 8)) imm);
      BitVec.and rs1_val immext := by rfl


-- 4 tried to prove addition
/-theorem MUL_bitvec : execute_MUL_pure64 { high := false, signed_rs1 := false, signed_rs2 := false } (reg1 : BitVec 64) (reg2 : BitVec 64) = BitVec.mul reg2 reg1 := by
  unfold execute_MUL_pure64
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.mul_eq]
  simp [Functions.xlen]
  have h1 : (2 : Int) * (2 ^(3 : Int) * 8) = 128 := by rfl --such that types match
  rw [h1]
  simp [Sail.BitVec.extractLsb]
  simp [to_bits]
  simp [ get_slice_int]
  simp [BitVec.extractLsb]
  simp [extractLsb'_extractLsb'2]
  unfold HPow.hPow
  unfold instHPowInt_leanRV64DLEAN
  simp
  have h2: min 64 128 = 64 := by rfl
  rw [h2]
  unfold HMul.hMul
  unfold HAdd.hAdd
  unfold Int.instMax
  sorry-/

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

---- ZBB extensions extraction to pure bit vectors

theorem execute_ZBB_RTYPEW_pure64_RISCV_ROLW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  execute_ZBB_RTYPEW_pure64 rs2_val rs1_val bropw_zbb.RISCV_ROLW
    = BitVec.signExtend 64
    (BitVec.or (BitVec.shiftLeft (BitVec.setWidth 32 rs1_val) (BitVec.extractLsb 4 0 rs2_val).toNat)
      (BitVec.ushiftRight (BitVec.setWidth 32 rs1_val) (
        ((BitVec.sub ((BitVec.extractLsb' 0 (5)
            (BitVec.ofInt (6)
              (32))))
          (BitVec.extractLsb 4 0 rs2_val)))).toNat))
     := by rfl

theorem execute_ZBB_RTYPEW_pure64_RISCV_RORW(rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  execute_ZBB_RTYPEW_pure64 rs2_val rs1_val bropw_zbb.RISCV_RORW
    = BitVec.signExtend (64)
    (BitVec.or (BitVec.ushiftRight (BitVec.setWidth 32 rs1_val) (rs2_val.toNat % 32))
      (BitVec.shiftLeft (BitVec.setWidth 32 rs1_val)
        ((2 ^ 5 - rs2_val.toNat % 32 +
            BitVec.length (BitVec.setWidth 32 rs1_val) % 2 ^ (5 + 1)) %
          2 ^ 5)))
     := by
    unfold execute_ZBB_RTYPEW_pure64
    simp
    unfold Functions.sign_extend  Sail.BitVec.signExtend Functions.rotate_bits_right shift_bits_right
         Sail.BitVec.extractLsb shift_bits_left Functions.to_bits get_slice_int
    simp
    rfl

    --unfold HOr.hOr instHOrBitVec_leanRV64DLEAN
    --simp

-- extract byte or halfwords and either sign or zero extend it
theorem execute_ZBB_EXTOP_pure64_RISCV_SEXTB (rs1_val : BitVec 64) :
    execute_ZBB_EXTOP_pure64 rs1_val extop_zbb.RISCV_SEXTB
      = BitVec.signExtend 64 (BitVec.extractLsb 7 0 rs1_val) := by rfl

theorem execute_ZBB_EXTOP_pure64_RISCV_SEXTH (rs1_val : BitVec 64) :
    execute_ZBB_EXTOP_pure64 rs1_val extop_zbb.RISCV_SEXTH
      = BitVec.signExtend 64 (BitVec.extractLsb 15 0 rs1_val)  := by rfl

theorem execute_ZBB_EXTOP_pure64_RISCV_ZEXTH (rs1_val : BitVec 64) :
    execute_ZBB_EXTOP_pure64 rs1_val extop_zbb.RISCV_ZEXTH
      = BitVec.zeroExtend 64 (BitVec.extractLsb 15 0 rs1_val) := by rfl


theorem execute_ZBB_RTYPE_pure_RISCV_ROL (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  execute_ZBB_RTYPE_pure (rs2_val) (rs1_val ) (brop_zbb.RISCV_ROL) =
   BitVec.or (BitVec.shiftLeft  rs1_val (BitVec.extractLsb 5 0 rs2_val).toNat)
    (BitVec.ushiftRight rs1_val  (BitVec.extractLsb' 0 6 (BitVec.ofInt (7) (64)) - BitVec.extractLsb 5 0 rs2_val).toNat)
  :=
  by
  unfold execute_ZBB_RTYPE_pure
  simp
  unfold Sail.BitVec.extractLsb rotate_bits_left shift_bits_left shift_bits_right to_bits BitVec.length get_slice_int
  rfl

theorem execute_ZBB_RTYPE_pure_RISCV_ROR (rs2_val : BitVec 64) (rs1_val : BitVec 64)  :
  execute_ZBB_RTYPE_pure (rs2_val) (rs1_val ) (brop_zbb.RISCV_ROR) =
    BitVec.or (BitVec.ushiftRight rs1_val (BitVec.extractLsb 5 0 rs2_val).toNat)
    (BitVec.shiftLeft rs1_val ((BitVec.extractLsb' 0 6 (BitVec.ofInt (7) (64)) - BitVec.extractLsb 5 0 rs2_val)).toNat)
   :=
  by
  unfold execute_ZBB_RTYPE_pure
  simp
  unfold rotate_bits_right Sail.BitVec.extractLsb shift_bits_left to_bits get_slice_int shift_bits_right BitVec.length
  rfl

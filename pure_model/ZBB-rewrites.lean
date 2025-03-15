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

-- SIMPLIFICATION OF RISC-V EXTENSION, had to translate into bit vec form

-- ZBB EXTENSION
theorem execute_ZBB_RTYPEW_pure64_RISCV_ROLW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  execute_ZBB_RTYPEW_pure64 rs2_val rs1_val bropw_zbb.RISCV_ROLW
    = BitVec.signExtend 64
    (BitVec.or (BitVec.setWidth 32 rs1_val <<< BitVec.extractLsb 4 0 rs2_val)
      (BitVec.setWidth 32 rs1_val >>>
        (BitVec.extractLsb' 0 (BitVec.length (BitVec.extractLsb 4 0 rs2_val))
            (BitVec.ofInt (0 + BitVec.length (BitVec.extractLsb 4 0 rs2_val) + 1)
              ((BitVec.length (BitVec.setWidth 32 rs1_val)))) -
          BitVec.extractLsb 4 0 rs2_val)))
     := by rfl

--TO DO ASK IF INSTANCE IS CORRECT BV UNSURE
theorem execute_ZBB_RTYPEW_pure64_RISCV_RORW(rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  execute_ZBB_RTYPEW_pure64 rs2_val rs1_val bropw_zbb.RISCV_RORW
    = BitVec.signExtend (2 ^ 3 * 8)
    (BitVec.or (BitVec.setWidth 32 rs1_val >>> (rs2_val.toNat % 32))
      (BitVec.setWidth 32 rs1_val <<<
        ((2 ^ BitVec.length (BitVec.extractLsb 4 0 rs2_val) - rs2_val.toNat % 32 +
            BitVec.length (BitVec.setWidth 32 rs1_val) % 2 ^ (BitVec.length (BitVec.extractLsb 4 0 rs2_val) + 1)) %
          2 ^ BitVec.length (BitVec.extractLsb 4 0 rs2_val))))
     := by
    unfold execute_ZBB_RTYPEW_pure64
    simp
    unfold sign_extend Sail.BitVec.signExtend rotate_bits_right shift_bits_right Sail.BitVec.extractLsb shift_bits_left to_bits get_slice_int
    simp
    --unfold HOr.hOr instHOrBitVec_leanRV64DLEAN
    --simp
    rfl

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

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

/-!
## Content
This file contains the rewrites from the pure function corrresponding to`ZBA extension` instruction semantics
into a bit-vector only representation.

This BitVec representation is used in the `RISCV64` dialect in `Lean-MLIR` project to define the semantics
of the corresponding RISC-V operations.
-/


-- shifts unsigned word by some specifc amount and adds rs2_val
theorem execute_ZBA_RTYPEUW_pure64_RISCV_ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_ZBA_RTYPEUW_pure64 rs2_val rs1_val bropw_zba.RISCV_ADDUW
      = BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1_val) <<< 0#2 + rs2_val
       := by
  unfold execute_ZBA_RTYPEUW_pure64
  simp
  unfold shift_bits_left Sail.BitVec.extractLsb zero_extend Sail.BitVec.zeroExtend HPow.hPow instHPowInt_leanRV64DLEAN
  simp only [Int.reduceToNat, Int.reducePow, Int.reduceMul, BitVec.truncate_eq_setWidth,
    BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, BitVec.shiftLeft_zero]

theorem execute_ZBA_RTYPEUW_pure64_RISCV_SH1ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_ZBA_RTYPEUW_pure64 rs2_val rs1_val bropw_zba.RISCV_SH1ADDUW
      = BitVec.add (BitVec.zeroExtend (Int.toNat 64) (BitVec.extractLsb 31 0 rs1_val) <<< 1#2)  (rs2_val)
  := by
  unfold execute_ZBA_RTYPEUW_pure64
  simp
  unfold shift_bits_left Sail.BitVec.extractLsb zero_extend Sail.BitVec.zeroExtend HPow.hPow instHPowInt_leanRV64DLEAN
  rfl

theorem execute_ZBA_RTYPEUW_pure64_RISCV_SH2ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_ZBA_RTYPEUW_pure64 rs2_val rs1_val bropw_zba.RISCV_SH2ADDUW
      = BitVec.zeroExtend (Int.toNat 64) (BitVec.extractLsb 31 0 rs1_val) <<< 2#2 + rs2_val
  := by
  unfold execute_ZBA_RTYPEUW_pure64
  simp
  unfold shift_bits_left Sail.BitVec.extractLsb zero_extend Sail.BitVec.zeroExtend HPow.hPow instHPowInt_leanRV64DLEAN
  rfl

theorem execute_ZBA_RTYPEUW_pure64_RISCV_SH3ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_ZBA_RTYPEUW_pure64 rs2_val rs1_val bropw_zba.RISCV_SH3ADDUW
      = BitVec.zeroExtend (Int.toNat 64) (BitVec.extractLsb 31 0 rs1_val) <<< 3#2 + rs2_val
  := by
  unfold execute_ZBA_RTYPEUW_pure64
  simp
  unfold shift_bits_left Sail.BitVec.extractLsb zero_extend Sail.BitVec.zeroExtend HPow.hPow instHPowInt_leanRV64DLEAN
  rfl

theorem execute_ZBA_RTYPE_pure64_RISCV_SH1ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_ZBA_RTYPE_pure64 rs2_val rs1_val brop_zba.RISCV_SH1ADD
    = BitVec.add (rs1_val <<< 1#2) rs2_val := by rfl

theorem execute_ZBA_RTYPE_pure64_RISCV_SH2ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_ZBA_RTYPE_pure64 rs2_val rs1_val brop_zba.RISCV_SH2ADD
    = BitVec.add (rs1_val <<< 2#2) rs2_val:= by rfl

theorem execute_ZBA_RTYPE_pure64_RISCV_SH3ADD(rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_ZBA_RTYPE_pure64 rs2_val rs1_val brop_zba.RISCV_SH3ADD
    = BitVec.add (rs1_val <<< 3#2) rs2_val:= by rfl

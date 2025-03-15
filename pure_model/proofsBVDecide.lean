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

-- COLLECTION OF PROOFS THAT CAN BE DONE WITH BV_DECIDE VERY SMOOTHLY AND NOT WITH RFL ETC.

--1. using Bv_decide
theorem execute_RTYPE_pure64__RISCV_AND (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPE_pure64 rop.RISCV_AND rs2_val rs1_val
    = BitVec.and rs2_val rs1_val := by
  unfold PureFunctions.execute_RTYPE_pure64
  bv_decide

-- 1. no possible by rfl etc
theorem execute_RTYPE_pure64__RISCV_AND1 (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPE_pure64 rop.RISCV_AND rs2_val rs1_val
    = BitVec.and rs2_val rs1_val := by
  unfold PureFunctions.execute_RTYPE_pure64
  --rfl
  sorry 

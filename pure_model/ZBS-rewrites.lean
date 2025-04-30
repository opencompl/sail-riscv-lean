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
This file contains the rewrites from the pure function corrresponding to`ZBS extension` instruction semantics
into a bit-vector only representation.

This BitVec representation is used in the `RISCV64` dialect in `Lean-MLIR` project to define the semantics
of the corresponding RISC-V operations.
-/


 theorem execute_ZBS_RTYPE_pure64_RISCV_BCLR (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BCLR
      = BitVec.and rs1_val (BitVec.not (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb  5 0 rs2_val).toNat))
  := by
  rfl

theorem execute_ZBS_RTYPE_pure64_RISCV_BEXT (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BEXT
      = BitVec.setWidth 64
    (match
      BitVec.and rs1_val (BitVec.shiftLeft (BitVec.setWidth 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat) !=
        0#64 with
    | true => 1#1
    | false => 0#1) := by rfl

-- inverts the bit at the index given by the least signficant 6 bits in rs2_val
theorem execute_ZBS_RTYPE_pure64_BINV (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BINV
      = BitVec.xor rs1_val  (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat) := by rfl

-- tried to proof using bv_decide ASK WHY BV_DECIDE DOESNT SUCCED IN THIS PROOF
theorem execute_ZBS_RTYPE_pure64_bvD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      execute_ZBS_RTYPE_pure64 rs2_val rs1_val  brop_zbs.RISCV_BINV
      = BitVec.xor rs1_val  (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat)
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
      = BitVec.or rs1_val (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat)
  := by
  unfold PureFunctions.execute_ZBS_RTYPE_pure64
  simp
  unfold Sail.BitVec.extractLsb shift_bits_left zero_extend Sail.BitVec.zeroExtend
  simp only [BitVec.truncate_eq_setWidth, BitVec.shiftLeft_eq', Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow]
  unfold HPow.hPow instHPowInt_leanRV64DLEAN
  bv_decide -- or using rfl works to.


theorem execute_ZBS_IOP_pure64_RISCV_BCLRI (shamt : BitVec 6) (rs1_val : BitVec 64) :
  execute_ZBS_IOP_pure64 shamt rs1_val biop_zbs.RISCV_BCLRI
  = BitVec.and rs1_val (BitVec.not (BitVec.shiftLeft (BitVec.setWidth 64 1#1) (shamt.toNat))):= by --rfl would also work
    unfold PureFunctions.execute_ZBS_IOP_pure64
    simp
    unfold shift_bits_left zero_extend Sail.BitVec.zeroExtend
    rfl

theorem execute_ZBS_IOP_pure64_RISCV_BEXTI (shamt : BitVec 6) (rs1_val : BitVec 64) :
  execute_ZBS_IOP_pure64 shamt rs1_val biop_zbs.RISCV_BEXTI
    = BitVec.setWidth 64
      (match (BitVec.and (rs1_val) (BitVec.shiftLeft (BitVec.setWidth 64 1#1) shamt.toNat)) != 0#64 with
      | true => 1#1
      | false => 0#1)
  := by rfl

theorem execute_ZBS_IOP_pure64_RISCV_BINVI (shamt : BitVec 6) (rs1_val : BitVec 64) :
    execute_ZBS_IOP_pure64 shamt rs1_val biop_zbs.RISCV_BINVI
    = BitVec.xor rs1_val  (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) shamt.toNat)
  := by rfl

theorem execute_ZBS_IOP_pure64_RISCV_BSETI (shamt : BitVec 6) (rs1_val : BitVec 64) :
  execute_ZBS_IOP_pure64 shamt rs1_val biop_zbs.RISCV_BSETI
  = BitVec.or rs1_val (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) shamt.toNat) := by rfl

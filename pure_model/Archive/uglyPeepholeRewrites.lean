
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


-- SOME INITIAL UGLY PROOFS ABOUT SIMPLE PEEPHOLE REWRITES WITHOUT USING AUTOMATION AND MY GENERAL MODELL :


-- @[simp]
theorem extractLsb'_extractLsb' :
    BitVec.extractLsb' start length (BitVec.extractLsb' start' length' x)
    = (BitVec.extractLsb' (start'+start) (min length length') x).setWidth length := by
  sorry

-- @[simp]
theorem extractLsb'_extractLsb'2 {x : BitVec w} :
    BitVec.extractLsb' start length (BitVec.extractLsb' start' length' x)
    = BitVec.extractLsb' (start'+start) length (x.setWidth (start + start' + (min length length'))) := by
  -- obtain rfl : w = 16 := sorry
  -- bv_decide
  sorry

theorem extractLsb'_zero : BitVec.extractLsb' 0 length x  = BitVec.setWidth length x := by
  sorry


theorem setWidth_extractLsb' (n w: Nat) (x : BitVec w) (h : n <= w) :
    BitVec.setWidth n x = BitVec.extractLsb' 0 n x := by
      simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]

-- proved the sign extension of zero vector is again zero
theorem  sign_extend_zero (w1 w2 : Nat) (h : w1 ≤ w2) :
    sign_extend (0#w1)   = 0#w2 := by
    rw [sign_extend]
    rw [Sail.BitVec.signExtend]
    rw [BitVec.signExtend]
    simp

theorem add_set_Width_eq (x : BitVec w1) (y : BitVec w1) :
    BitVec.add x y =  x + y  := by
      simp
      simp only [HAdd.hAdd, BitVec.setWidth_eq]

theorem add_set_Width (x : BitVec w1) (y : BitVec w2) :
    BitVec.add x y =  x + y  := by
      simp [HAdd.hAdd]


 --  MUL 0 rs1 rd = 0
theorem zero_MUL :  execute_MUL_pure64 { high := false, signed_rs1 := false, signed_rs2 := false } 0#64 (reg1 : BitVec 64) = 0#64 := by
  unfold execute_MUL_pure64
  simp
  simp [Functions.xlen]
  have h1 : (2 : Int) * (2 ^(3 : Int) * 8) = 128 := by rfl --such that types match
  rw [h1]
  simp only [Int.reduceToNat] --yields expression thats definitionally equal
  rfl

theorem MUL_zero :  execute_MUL_pure64 { high := false, signed_rs1 := false, signed_rs2 := false } (reg2 : BitVec 64) 0#64 = 0#64 := by
  unfold execute_MUL_pure64
  simp
  simp [Functions.xlen]
  have h1 : (2 : Int) * (2 ^(3 : Int) * 8) = 128 := by rfl --such that types match
  rw [h1]
  simp only [Int.reduceToNat] --yields expression thats definitionally equal
  rfl



theorem one_MUL :  execute_MUL_pure64 { high := false, signed_rs1 := false, signed_rs2 := false } 1#64 (reg1 : BitVec 64) = reg1 := by
  unfold execute_MUL_pure64
  simp
  simp [Functions.xlen]
  have h1 : (2 : Int) * (2 ^(3 : Int) * 8) = 128 := by rfl --such that types match
  rw [h1]
  simp
  unfold to_bits
  unfold get_slice_int
  simp [Sail.BitVec.extractLsb]
  simp [BitVec.extractLsb]
  simp [extractLsb'_extractLsb'2]
  --rw [BitVec.setWidth_eq]
  --dsimp [BitVec.setWidth_eq]
  simp [extractLsb'_zero]
  rw [BitVec.setWidth_setWidth]
  · rfl -- how to do case distinctions
  · omega -- used to proof omega terms


theorem MUL_one :  execute_MUL_pure64 { high := false, signed_rs1 := false, signed_rs2 := false } 1#64 (reg1 : BitVec 64) = reg1 := by
  unfold execute_MUL_pure64
  simp
  simp [Functions.xlen]
  have h1 : (2 : Int) * (2 ^(3 : Int) * 8) = 128 := by rfl --such that types match
  rw [h1]
  simp
  unfold to_bits
  unfold get_slice_int
  simp [Sail.BitVec.extractLsb]
  simp [BitVec.extractLsb]
  simp [extractLsb'_extractLsb'2]
  simp [extractLsb'_zero]
  rw [BitVec.setWidth_setWidth]
  . rfl
  . omega

theorem zero_add : execute_ADDIW_pure64 (0#12) (rs1 : (BitVec 64)) = BitVec.signExtend 64 (BitVec.setWidth 32 rs1) := by
  unfold execute_ADDIW_pure64
  rw [sign_extend_zero]
  . simp only [Nat.sub_zero, Nat.reduceAdd]
    rw [sign_extend]
    rw [Sail.BitVec.signExtend]
    simp only [Sail.BitVec.extractLsb]
    rw[BitVec.extractLsb]
    rw[← setWidth_extractLsb']
    . simp only [Nat.sub_zero, Nat.reduceAdd]
      rw [← add_set_Width_eq]
      unfold HPow.hPow
      unfold instHPowInt_leanRV64DLEAN
      bv_decide
    · simp only [Nat.sub_zero, Nat.reduceAdd, Nat.reduceLeDiff]
  .simp
   omega

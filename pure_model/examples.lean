
 /-simp
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
 example rewrites

     --have x : ((2:Int) ^ (3:Int) * 8).toNat = 64 := rfl
      --dsimp!
      --intros

-- in this file we are trying to proof some simple potential peephole rewrites
/-
example (f : BitVec 32 -> BitVec 32) (x : α) (h : α = BitVec 32) (y : BitVec 32) :
    f y = y := by
  rw [← h] at y

--@[simp]
theorem foo :  execute_MUL_pure64 { high := false, signed_rs1 := false, signed_rs2 := false } 0#64 1#64 = 0#64 := by
  sorry
  --unfold execute_MUL_pure64
  --simp
  --simp [Functions.xlen]
  --have h1 : (2 : Int) * (2 ^(3 : Int) * 8) = 128 := by rfl
  --rw [h1]
  --have h2 :  ((2 : Int) ^(3 : Int) * 8 -1) = 63 := by rfl
  --simp only [Int.reduceToNat, to_bits, get_slice_int, Nat.reduceAdd, Int.toNat_zero,
    --Int.Nat.cast_ofNat_Int, BitVec.ofInt_ofNat, BitVec.reduceExtracLsb']
  --simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, Nat.reducePow,
    --Nat.zero_mod, Nat.shiftRight_zero]
  --rfl
-- #print axioms foo
-/


    -/

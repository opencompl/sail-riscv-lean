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

-- pure functions modell <-> pure BitVec domain lowering


-- missing BitVector Lemmas:
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
  --unfold BitVec.extractLsb'
  --simp
  sorry


theorem extractLsb'_zero : BitVec.extractLsb' 0 length x  = BitVec.setWidth length x := by
  unfold BitVec.extractLsb'
  simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat]


theorem setWidth_extractLsb' (n w: Nat) (x : BitVec w) :
    BitVec.setWidth n x = BitVec.extractLsb' 0 n x := by
      simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]

-- proved the sign extension of zero vector is again zero
theorem  sign_extend_zero (w1 w2 : Nat) (h : w1 ≤ w2) :
    sign_extend (0#w1)   = 0#w2 := by
    rw [sign_extend]
    rw [Sail.BitVec.signExtend]
    rw [BitVec.signExtend]
    simp


-- SAIL FIX: to overcome the redefinition of operators in SAIL

theorem add_set_Width_eq (x : BitVec w1) (y : BitVec w1) :
    BitVec.add x y =  x + y  := by
      simp
      simp only [HAdd.hAdd, BitVec.setWidth_eq]

theorem add_set_Width (x : BitVec w1) (y : BitVec w2) :
    BitVec.add x y =  x + y  := by
      simp [HAdd.hAdd]


-- SECTION WHERE I PROVE THAT EACH RISC-V INSTRUCTION CORRESPONDS TO SIMPLER BIT VECTOR INSTRUCTIONS
-- SIMPLIFICATION OF RISC-V SEMANTICS TO BITVECTORS and writting coorespodnig proofs
-- pure functions modell <-> pure BitVec domain lowering

theorem execute_ADDIW_pure64_BitVec (imm : BitVec 12) (rs1_val : BitVec 64) :
  PureFunctions.execute_ADDIW_pure64 imm rs1_val =
     BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val)) := by
  unfold PureFunctions.execute_ADDIW_pure64
  simp
  unfold sign_extend
  unfold Sail.BitVec.signExtend
  unfold Sail.BitVec.extractLsb
  rw [BitVec.extractLsb]
  rw [← setWidth_extractLsb']
  unfold HPow.hPow
  unfold instHPowInt_leanRV64DLEAN
  bv_decide


-- loads immediate into upper 20 bits and then fills the rest up with 0 and returns it as the result
theorem execute_UTYPE_pure64_lui (imm : BitVec 20) (pc : BitVec 64) : PureFunctions.execute_UTYPE_pure64 imm pc (uop.RISCV_LUI)
    = BitVec.signExtend 64 (imm ++ (0x000 : (BitVec 12))) := by
  unfold PureFunctions.execute_UTYPE_pure64
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  unfold sign_extend Sail.BitVec.signExtend BitVec.signExtend
  unfold HAppend.hAppend HPow.hPow instHPowInt_leanRV64DLEAN BitVec.instHAppendHAddNat
  bv_decide

-- loads immediate into upper 20 bits and then fills the rest up with 0 and returns, adds the program counter and then returns it as a result
theorem execute_UTYPE_pure64_AUIPC (imm : BitVec 20) (pc : BitVec 64)  : PureFunctions.execute_UTYPE_pure64 imm pc (uop.RISCV_AUIPC)
    = BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x000 : (BitVec 12)))) pc := by
  unfold PureFunctions.execute_UTYPE_pure64
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_eq, BitVec.add_left_inj]
  unfold sign_extend Sail.BitVec.signExtend BitVec.signExtend
  unfold HAppend.hAppend HPow.hPow instHPowInt_leanRV64DLEAN BitVec.instHAppendHAddNat
  bv_decide


-- shiftiwop semantics:
theorem execute_SHIFTIWOP_pure64_RISCV_SLLIW (shamt : BitVec 5) (rs1_val : BitVec 64) :  PureFunctions.execute_SHIFTIWOP_pure64 shamt (sopw.RISCV_SLLIW) rs1_val
    = BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.extractLsb' 0 32 rs1_val) (shamt).toNat) := by
  unfold PureFunctions.execute_SHIFTIWOP_pure64
  simp only [BitVec.shiftLeft_eq]
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb  BitVec.signExtend
  rw [BitVec.extractLsb]
  unfold  shift_bits_left HPow.hPow HShiftLeft.hShiftLeft BitVec.instHShiftLeftNat instHPowInt_leanRV64DLEAN BitVec.instHShiftLeft
  bv_decide


-- logical rightshift, filled with zeros x/2^s rounding down
theorem execute_SHIFTIWOP_pure64_RISCV_SRLIW (shamt : BitVec 5) (rs1_val : BitVec 64)  :  PureFunctions.execute_SHIFTIWOP_pure64 shamt (sopw.RISCV_SRLIW) rs1_val
    = BitVec.signExtend 64 (BitVec.ushiftRight (BitVec.extractLsb' 0 32 rs1_val) (shamt).toNat) := by
  unfold PureFunctions.execute_SHIFTIWOP_pure64
  simp only [BitVec.ushiftRight_eq]
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb  BitVec.signExtend
  rw [BitVec.extractLsb]--- to rewrite into Lsb'
  unfold  shift_bits_right HPow.hPow HShiftRight.hShiftRight  instHPowInt_leanRV64DLEAN BitVec.instHShiftRightNat BitVec.instHShiftRight
  bv_decide

-- arithmetic rightshift, x.toInt >>> shamt

theorem execute_SHIFTIWOP_pure64_RISCV_SRAIW (shamt : BitVec 5) (rs1_val : BitVec 64) :
  PureFunctions.execute_SHIFTIWOP_pure64 shamt sopw.RISCV_SRAIW rs1_val
    =
    BitVec.signExtend 64
      (BitVec.setWidth 32
       (BitVec.extractLsb
         (31 + shamt.toNat)
          shamt.toNat
          (BitVec.signExtend (32 + shamt.toNat) (BitVec.extractLsb 31 0 rs1_val))
        )
      ) := by rfl

theorem execute_SHIFTIOP_pure64_RISCV_SLLI (shamt : BitVec 6) (rs1_val : BitVec 64)  : PureFunctions.execute_SHIFTIOP_pure64 shamt sop.RISCV_SLLI rs1_val
    = BitVec.shiftLeft rs1_val shamt.toNat := by
  unfold PureFunctions.execute_SHIFTIOP_pure64
  simp
  unfold shift_bits_left HShiftLeft.hShiftLeft BitVec.instHShiftLeft BitVec.instHShiftLeftNat
  bv_decide

theorem execute_SHIFTIOP_pure64_RISCV_SRLI (shamt : BitVec 6) (rs1_val : BitVec 64) : PureFunctions.execute_SHIFTIOP_pure64 shamt sop.RISCV_SRLI rs1_val
    = BitVec.ushiftRight rs1_val shamt.toNat := by
  unfold PureFunctions.execute_SHIFTIOP_pure64
  simp
  unfold shift_bits_right HShiftRight.hShiftRight BitVec.instHShiftRight BitVec.instHShiftRightNat
  bv_decide

theorem execute_SHIFTIOP_pure64_RISCV_SRAI (shamt : (BitVec 6)) (rs1_val : (BitVec 64)) : PureFunctions.execute_SHIFTIOP_pure64 shamt sop.RISCV_SRAI rs1_val =
    let value := rs1_val ;
    let shift := shamt.toNat;
    BitVec.setWidth 64 (BitVec.extractLsb (63 + shift)  shift  (BitVec.signExtend ((64 + shift)) value)):=
  by
  rfl

-- simple integer operations on 32-bit word and then sign extend result to 64 bits
theorem execute_RTYPEW_pure64_RISCV_ADDW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPEW_pure64 ropw.RISCV_ADDW rs2_val rs1_val =
      let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
      let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
      BitVec.signExtend 64 (BitVec.add rs1_val32 rs2_val32)  := by
  unfold PureFunctions.execute_RTYPEW_pure64
  simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.add_eq]
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb HPow.hPow instHPowInt_leanRV64DLEAN
  bv_decide


theorem execute_RTYPEW_pure64_RISCV_SUBW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPEW_pure64 (ropw.RISCV_SUBW) (rs2_val) (rs1_val) =
      let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
      let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
      BitVec.signExtend 64 (BitVec.sub rs1_val32 rs2_val32)  := by
    unfold PureFunctions.execute_RTYPEW_pure64
    simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.sub_eq]
    unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb HPow.hPow instHPowInt_leanRV64DLEAN
    bv_decide

-- can be all done by rfl
theorem execute_RTYPEW_pure64_RISCV_SLLW (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPEW_pure64 ropw.RISCV_SLLW rs2_val rs1_val =
    let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
    let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
    let shamt := BitVec.extractLsb' 0 5 rs2_val32;
    BitVec.signExtend 64 (BitVec.shiftLeft rs1_val32 shamt.toNat) := by
  --rfl
  unfold PureFunctions.execute_RTYPEW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb BitVec.signExtend
  unfold  shift_bits_left HPow.hPow HShiftLeft.hShiftLeft BitVec.instHShiftLeftNat instHPowInt_leanRV64DLEAN BitVec.instHShiftLeft
  simp only [Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, BitVec.toInt_shiftLeft,
    BitVec.extractLsb'_toNat, BitVec.shiftLeft_eq]

-- can be all done by rfl
theorem execute_RTYPEW_pure64_RISCV_SRLW (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPEW_pure64 ropw.RISCV_SRLW rs2_val rs1_val
    = let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
    let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
    let shamt := BitVec.extractLsb' 0 5 rs2_val32;
    BitVec.signExtend 64 (BitVec.ushiftRight rs1_val32 shamt.toNat)  := by
  --rfl
  unfold PureFunctions.execute_RTYPEW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb BitVec.signExtend
  rw [BitVec.extractLsb]
  unfold  shift_bits_right HPow.hPow HShiftRight.hShiftRight BitVec.instHShiftRightNat instHPowInt_leanRV64DLEAN BitVec.instHShiftRight
  simp only [Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.sub_zero, Nat.reduceAdd,
  BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, BitVec.toInt_ushiftRight,
  BitVec.extractLsb'_toNat, BitVec.ushiftRight_eq]


-- SUBSECTION WHERE MADE THEOIREMS FOR REWRITTING TO THE CORE INSTANCE

@[simp] theorem sail_hPow_eq (x y : Int) : x ^ y  = x ^ y.toNat := by rfl

-- very ugly
theorem execute_RTYPEW_pure64_RISCV_SRAW (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :
    PureFunctions.execute_RTYPEW_pure64 (ropw.RISCV_SRAW) rs2_val rs1_val
      = BitVec.signExtend 64
           (BitVec.setWidth 32
              (BitVec.extractLsb
                 (31 + rs2_val.toNat % 4294967296 % 32)
                     (rs2_val.toNat % 4294967296 % 32)
                          (BitVec.signExtend (32 + rs2_val.toNat % 4294967296 % 32)
                              (BitVec.extractLsb 31 0 rs1_val)))) := by rfl


theorem execute_RTYPE_pure64_RISCV_ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_ADD  rs2_val rs1_val
      = BitVec.add rs1_val rs2_val := by rfl

theorem execute_RTYPE_pure64_RISCV_SLT (rs2_val : BitVec 64) (rs1_val : BitVec 64) : PureFunctions.execute_RTYPE_pure64 rop.RISCV_SLT rs2_val rs1_val
  =  let b := BitVec.slt rs1_val rs2_val;
    BitVec.setWidth 64 (BitVec.ofBool b)  := by rfl

theorem execute_RTYPE_pure64_RISCV_SLTU (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_SLTU rs2_val rs1_val
    = let b := BitVec.ult rs1_val rs2_val;
      BitVec.setWidth 64 (BitVec.ofBool b)  := by rfl

theorem execute_RTYPE_pure64_RISCV_AND (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_AND rs2_val rs1_val
      = BitVec.and rs2_val rs1_val := by
  unfold PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_OR(rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_OR  rs2_val rs1_val
      = BitVec.or rs2_val rs1_val := by
  unfold PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_XOR(rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_XOR  rs2_val  rs1_val
      = BitVec.xor rs2_val rs1_val := by
  unfold PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_SLL (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
     PureFunctions.execute_RTYPE_pure64 rop.RISCV_SLL  rs2_val rs1_val =
       let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
       BitVec.shiftLeft rs1_val shamt := by rfl

theorem execute_RTYPE_pure64_RISCV_SRL (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_SRL rs2_val rs1_val
      = let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
      BitVec.ushiftRight rs1_val shamt := by rfl

theorem execute_RTYPE_pure64_RISCV_SUB (rs2_val : BitVec 64) (rs1_val : BitVec 64) : PureFunctions.execute_RTYPE_pure64 rop.RISCV_SUB  rs2_val rs1_val
    = BitVec.sub rs1_val rs2_val  := by
  unfold PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_SRA (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_SRA rs2_val rs1_val
      = BitVec.setWidth 64
      (BitVec.extractLsb
        (63 + (BitVec.extractLsb 5 0 rs2_val).toNat)
        (BitVec.extractLsb 5 0 rs2_val).toNat
        (BitVec.signExtend
          (64 + (BitVec.extractLsb 5 0 rs2_val).toNat) rs1_val)):= by rfl

theorem execute_REMW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_REMW_pure64 False rs2_val rs1_val
    = BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (Int.ofNat
          (if Int.ofNat (BitVec.extractLsb 31 0 rs2_val).toNat = 0 then Int.ofNat (BitVec.extractLsb 31 0 rs1_val).toNat
            else
              (Int.ofNat (BitVec.extractLsb 31 0 rs1_val).toNat).tmod
                (Int.ofNat (BitVec.extractLsb 31 0 rs2_val).toNat)).toNat))):= by
  unfold execute_REMW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
  simp


theorem execute_REMW_pure64_signed :
    PureFunctions.execute_REMW_pure64 (True) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) =
      BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (Int.ofNat
          (if (BitVec.extractLsb 31 0 rs2_val).toInt = 0 then (BitVec.extractLsb 31 0 rs1_val).toInt
            else (BitVec.extractLsb 31 0 rs1_val).toInt.tmod (BitVec.extractLsb 31 0 rs2_val).toInt).toNat))):= by
  unfold execute_REMW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb to_bits get_slice_int
  rw [← Int.ofNat_eq_coe]
  simp

--tmod was hard
theorem execute_REM_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_REM_pure64 (False) rs2_val rs1_val =
   BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (Int.ofNat
        (if Int.ofNat rs2_val.toNat = 0 then Int.ofNat rs1_val.toNat
          else (Int.ofNat rs1_val.toNat).tmod (Int.ofNat rs2_val.toNat)).toNat))
  := by
  unfold execute_REM_pure64
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, Int.ofNat_eq_coe,
    Int.ofNat_toNat]
  unfold  to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe,← Int.ofNat_eq_coe]
  simp
  rfl


theorem execute_REM_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_REM_pure64 True rs2_val rs1_val
      = BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (Int.ofNat (if rs2_val.toInt = 0 then rs1_val.toInt else rs1_val.toInt.tmod rs2_val.toInt).toNat)) := by
  unfold execute_REM_pure64
  simp
  unfold  to_bits get_slice_int Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul]
  rw [← Int.ofNat_eq_coe]
  simp only [Int.reduceToNat, Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]


theorem  execute_MULW_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64))  : execute_MULW_pure64 rs2_val rs1_val =
    BitVec.signExtend 64
    (BitVec.extractLsb 31 0
      (BitVec.extractLsb' 0 64
        (BitVec.ofInt 65
          ((BitVec.extractLsb 31 0 rs1_val).toInt * (BitVec.extractLsb 31 0 rs2_val).toInt).toNat)))
     := by rfl

theorem execute_MUL_pure64_fff (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
     execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= False, signed_rs2 := False }) rs2_val rs1_val
       = BitVec.extractLsb 63 0
        (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (max (Int.mul (Int.ofNat rs1_val.toNat) (Int.ofNat rs2_val.toNat)) 0)))
        := by
        unfold  execute_MUL_pure64
        simp only [decide_false, Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_coe]
        unfold Sail.BitVec.extractLsb Functions.xlen to_bits get_slice_int
        simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub,
          Nat.reduceAdd, Int.ofNat_toNat, Int.mul_def]


--ASK .toNat
theorem execute_MUL_pure64_fft (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= False, signed_rs2 := True }) rs2_val rs1_val
      = BitVec.extractLsb 63 0
    (BitVec.extractLsb' 0 128
      (BitVec.ofInt 129 (Int.ofNat (Int.mul (Int.ofNat rs1_val.toNat)  (rs2_val.toInt)).toNat)))
    := by
    unfold execute_MUL_pure64
    simp only [decide_false, Bool.false_eq_true, ↓reduceIte, decide_true, Int.ofNat_eq_coe,
      Int.ofNat_toNat]
    unfold Sail.BitVec.extractLsb Functions.xlen
    simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
    unfold to_bits get_slice_int
    rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
    simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]
    --bv_decide ask why this can't be recognized by bv_decide

theorem execute_MUL_pure64_ftf (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= True, signed_rs2 := False }) rs2_val rs1_val
    = BitVec.extractLsb 63 0
      (BitVec.extractLsb' 0 128
        (BitVec.ofInt 129
        (Int.ofNat (Int.mul (BitVec.toInt rs1_val) (Int.ofNat (BitVec.toNat rs2_val))).toNat)))
    := by
    unfold execute_MUL_pure64
    simp only [decide_false, Bool.false_eq_true, ↓reduceIte, decide_true, Int.ofNat_eq_coe,
      Int.toNat_ofNat, Int.mul_def, Int.ofNat_toNat]
    unfold Sail.BitVec.extractLsb Functions.xlen
    simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
    unfold to_bits get_slice_int
    rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
    simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]

theorem execute_MUL_pure64_tff (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= False, signed_rs2 := False }) rs2_val rs1_val
      = BitVec.extractLsb 127 64
      (BitVec.extractLsb' 0 128
        (BitVec.ofInt 129 (Int.ofNat (Int.mul (Int.ofNat rs1_val.toNat) (Int.ofNat rs2_val.toNat)).toNat)))
  := by
  unfold execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, decide_false, Bool.false_eq_true, Int.ofNat_eq_coe,
    Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]

theorem execute_MUL_pure64_tft (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= False, signed_rs2 := True }) rs2_val rs1_val
      = BitVec.extractLsb 127 64
    (BitVec.extractLsb' 0 128
      (BitVec.ofInt 129 (Int.ofNat (Int.mul (Int.ofNat rs1_val.toNat) rs2_val.toInt).toNat)))
  := by
  unfold execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, decide_false, Bool.false_eq_true, Int.ofNat_eq_coe,
    Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]


theorem execute_MUL_pure64_ttf (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= True, signed_rs2 := False }) rs2_val rs1_val
      = BitVec.extractLsb 127 64
    (BitVec.extractLsb' 0 128
      (BitVec.ofInt 129 (Int.ofNat (Int.mul rs1_val.toInt (Int.ofNat rs2_val.toNat)).toNat)))
  := by
  unfold execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, decide_false, Bool.false_eq_true, Nat.reduceAdd,
    Int.ofNat_eq_coe, Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]


theorem execute_MUL_pure64_ftt (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= True, signed_rs2 := True }) rs2_val rs1_val
      = BitVec.extractLsb 63 0
    (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (Int.ofNat (Int.mul rs1_val.toInt rs2_val.toInt).toNat)))
  := by
  unfold execute_MUL_pure64
  simp
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]

theorem execute_MUL_pure64_ttt (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= True, signed_rs2 := True }) rs2_val rs1_val
      = BitVec.extractLsb 127 64
    (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (Int.ofNat (Int.mul rs1_val.toInt rs2_val.toInt).toNat)))
  := by
  unfold execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]


theorem execute_DIVW_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  PureFunctions.execute_DIVW_pure64 (True) rs2_val rs1_val
    = BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (max
          (if
              2147483647 <
                if (BitVec.extractLsb 31 0 rs2_val).toInt = 0 then -1
                else (BitVec.extractLsb 31 0 rs1_val).toInt.tdiv (BitVec.extractLsb 31 0 rs2_val).toInt then
            -2147483648
          else
            if (BitVec.extractLsb 31 0 rs2_val).toInt = 0 then -1
            else (BitVec.extractLsb 31 0 rs1_val).toInt.tdiv (BitVec.extractLsb 31 0 rs2_val).toInt)
          0)))
  := by
  unfold execute_DIVW_pure64
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, decide_true, ↓reduceIte,
    Nat.sub_zero, Nat.reduceAdd, beq_iff_eq, Int.reduceNeg, Int.reduceSub, gt_iff_lt, Bool.true_and,
    decide_eq_true_eq, Int.zero_sub]
  unfold sign_extend Sail.BitVec.signExtend to_bits get_slice_int Sail.BitVec.extractLsb
  simp only [Nat.reduceAdd, Int.reduceNeg, Int.ofNat_toNat]

--tdiv
theorem execute_DIVW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64)
    : PureFunctions.execute_DIVW_pure64 (False) rs2_val rs1_val
    =
    BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (Int.ofNat
          (if Int.ofNat (BitVec.extractLsb 31 0 rs2_val).toNat = 0 then -1
            else
              (Int.ofNat (BitVec.extractLsb 31 0 rs1_val).toNat).tdiv
                (Int.ofNat (BitVec.extractLsb 31 0 rs2_val).toNat)).toNat)))
  := by
  unfold execute_DIVW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend to_bits get_slice_int Sail.BitVec.extractLsb
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe ]
  simp



theorem execute_DIV_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
     execute_DIV_pure64 (True) rs2_val rs1_val
      = BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (max
        (if 9223372036854775807 < if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt then
          -9223372036854775808
        else if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt)
        0))
  := by
  unfold execute_DIV_pure64
  simp only [decide_true, ↓reduceIte, beq_iff_eq, Int.reduceNeg, gt_iff_lt, Bool.true_and,
    decide_eq_true_eq]
  unfold to_bits get_slice_int Functions.xlen xlen_max_signed xlen_min_signed
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.reduceAdd,
    Int.pred_toNat, Int.reduceNeg, Int.zero_sub, Int.ofNat_toNat]
  unfold Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.add_one_sub_one,
    Int.reduceSub, Int.reduceNeg]

-- adapt semantics
theorem execute_DIV_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64)
    : execute_DIV_pure64 (False) rs2_val rs1_val
    =  BitVec.extractLsb' 0 64
    (BitVec.ofNat 65
      (if Int.ofNat rs2_val.toNat = 0 then -1 else (Int.ofNat rs1_val.toNat).tdiv (Int.ofNat rs2_val.toNat)).toNat)
  := by
  unfold execute_DIV_pure64
  simp
  unfold to_bits get_slice_int Functions.xlen
  dsimp

theorem execute_ITYPE_pure64_RISCV_ADDI (imm : BitVec 12) (rs1_val : BitVec 64) : PureFunctions.execute_ITYPE_pure64 imm rs1_val iop.RISCV_ADDI
    = let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
    BitVec.add rs1_val immext := by
  unfold PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend --HPow.hPow instHPowInt_leanRV64DLEAN bc introdued the lemma
  bv_decide

theorem execute_ITYPE_pure64_RISCV_SLTI (imm : BitVec 12) (rs1_val : BitVec 64) :
     PureFunctions.execute_ITYPE_pure64 imm  rs1_val iop.RISCV_SLTI
       = let immext : BitVec 64 := (BitVec.signExtend 64 imm);
       let b := BitVec.slt rs1_val immext;
       BitVec.zeroExtend 64 (BitVec.ofBool b)  := by rfl

theorem execute_ITYPE_pure64_RISCV_SLTIU (imm : BitVec 12) (rs1_val : BitVec 64) :
     PureFunctions.execute_ITYPE_pure64 imm  rs1_val iop.RISCV_SLTIU
       = let immext : BitVec 64 := (BitVec.signExtend 64 imm);
       let b := BitVec.ult rs1_val immext;
       BitVec.setWidth 64 (BitVec.ofBool b)  := by rfl

-- works also by using rfl
theorem execute_ITYPE_pure64_RISCV_ANDI (imm : BitVec 12) (rs1_val : BitVec 64) :
    PureFunctions.execute_ITYPE_pure64 imm rs1_val  iop.RISCV_ANDI
      = let immext : BitVec 64 := (BitVec.signExtend 64 imm);
      BitVec.and rs1_val immext := by
  unfold PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend  HAnd.hAnd instHAndBitVec_leanRV64DLEAN
   instHAndOfAndOp
  bv_decide

-- works by using rfl
theorem execute_ITYPE_pure64_RISCV_ORI (imm : (BitVec 12)) (rs1_val : (BitVec 64))  :
    PureFunctions.execute_ITYPE_pure64 imm rs1_val (iop.RISCV_ORI)
      = let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
      BitVec.or rs1_val immext
  := by
  unfold PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

-- works by using rfl
theorem execute_ITYPE_pure64_RISCV_XORI imm (rs1_val : (BitVec 64))  :
    PureFunctions.execute_ITYPE_pure64 (imm : (BitVec 12)) (rs1_val : (BitVec 64)) (iop.RISCV_XORI)
      = let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
      BitVec.xor rs1_val immext
  := by
  unfold PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

theorem execute_ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :
    execute_ZICOND_RTYPE_pure64 rs2_val  rs1_val zicondop.RISCV_CZERO_EQZ
      = (if rs2_val = BitVec.zero 64 then BitVec.zero 64 else rs1_val)
  := by
  unfold execute_ZICOND_RTYPE_pure64
  simp
  unfold zeros_implicit
  rfl

theorem execute_ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :
    execute_ZICOND_RTYPE_pure64 rs2_val  rs1_val zicondop.RISCV_CZERO_NEZ
      = (if rs2_val = BitVec.zero 64 then rs1_val else BitVec.zero 64)
  := by
  unfold execute_ZICOND_RTYPE_pure64
  simp
  unfold zeros_implicit
  rfl


-- tested SIMPLE PEEPHOLE REWRITES:Prove simple rewrites based on the BitVector modelling

theorem  add_zero : PureFunctions.execute_ADDIW_pure64 (imm : BitVec 12) (0#64) =  BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) 0#64))  := by
  rw [execute_ADDIW_pure64_BitVec]

theorem  zero_add : PureFunctions.execute_ADDIW_pure64 (0#12) (x : BitVec 64) =  BitVec.signExtend 64 (BitVec.setWidth 32 x)  := by
  rw [execute_ADDIW_pure64_BitVec]
  bv_decide

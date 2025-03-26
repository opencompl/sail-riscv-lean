
import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
import LeanRV64DLEAN


set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Functions
open Retired
open Sail

 -- extracted a subset of (pure) functions
--14 functions

namespace PureFunctions
--purified
-- semantics: adds signed extended immediate to reg rs1 and prodcues sign-extension of 64 bit result in result register
def execute_ADDIW_pure64 (imm : (BitVec 12)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let result :=  rs1_val + (sign_extend (m := ((2 ^i 3) *i 8)) imm) -- rs1_val + sign extended immediate
  (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb result 31 0))


def execute_UTYPE_pure64 (imm : (BitVec 20)) (pc : (BitVec 64)) (op : uop)  : BitVec 64 :=
  let off : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) (imm ++ (0x000 : (BitVec 12)))) --loads immediate into upper 20 bits and then fills the rest up with 0
  let result := match op with
      | uop.RISCV_LUI => off
      | uop.RISCV_AUIPC => BitVec.add pc off
  result

def execute_SHIFTIWOP_pure64 (shamt : (BitVec 5)) (op : sopw) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb (rs1_val) 31 0
  let result : (BitVec 32) :=
    match op with
    | sopw.RISCV_SLLIW => (shift_bits_left rs1_val32 shamt)
    | sopw.RISCV_SRLIW => (shift_bits_right rs1_val32 shamt)
    | sopw.RISCV_SRAIW => (shift_bits_right_arith rs1_val32 shamt)
  (sign_extend (m := ((2 ^i 3) *i 8)) result) -- sign extend it to 64 bit again

def execute_SHIFTIOP_pure64 (shamt : (BitVec 6)) (op : sop) (rs1_val : (BitVec 64)) : BitVec 64 :=
      match op with
      | sop.RISCV_SLLI => (shift_bits_left rs1_val shamt)
      | sop.RISCV_SRLI => (shift_bits_right rs1_val shamt)
      | sop.RISCV_SRAI => (shift_bits_right_arith (rs1_val) shamt)


-- purified, *W suffix indicates that operates on the lower 32 bits, done
def execute_RTYPEW_pure64 (op : ropw) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let rs2_val32 :=  Sail.BitVec.extractLsb rs2_val 31 0
  let result : (BitVec 32) :=
    match op with
    | ropw.RISCV_ADDW => (rs1_val32 + rs2_val32)
    | ropw.RISCV_SUBW => (rs1_val32 - rs2_val32)
    | ropw.RISCV_SLLW => (shift_bits_left rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
    | ropw.RISCV_SRLW => (shift_bits_right rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
    | ropw.RISCV_SRAW => (shift_bits_right_arith rs1_val32 (Sail.BitVec.extractLsb rs2_val32 4 0))
  ((sign_extend (m := ((2 ^i 3) *i 8)) result)) -- sign extended the result to 64 bits again


-- purified,
def execute_RTYPE_pure64 (op : rop)  (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)): BitVec 64 :=
  let result :=
      match op with
      | rop.RISCV_ADD => rs1_val + rs2_val
      | rop.RISCV_SLT =>
        (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_s (rs1_val) (rs2_val)))) -- checks that lhs is less than rhs and set the bool accordingly
      | rop.RISCV_SLTU =>
         (zero_extend (m := ((2 ^i 3) *i 8))
            (bool_to_bits (zopz0zI_u (rs1_val) (rs2_val))))
      | rop.RISCV_AND => rs1_val &&& rs2_val
      | rop.RISCV_OR => rs1_val ||| rs2_val
      | rop.RISCV_XOR => rs1_val ^^^ rs2_val
      | rop.RISCV_SLL =>
        (shift_bits_left (rs1_val) --reason for log2.. etc is it extracts the lower 6 bits where the shift command is encoded
            (Sail.BitVec.extractLsb (rs2_val) (Functions.log2_xlen -i 1) 0)) --(log2_xlen -i 1) log2_xlen yields 6 thus overall extracts the last 5 bits
      | rop.RISCV_SRL =>
        (shift_bits_right (rs1_val)
            (Sail.BitVec.extractLsb (rs2_val) (Functions.log2_xlen -i 1) 0))
      | rop.RISCV_SUB => rs1_val - rs2_val
      | rop.RISCV_SRA =>
        (shift_bits_right_arith (rs1_val)
            (Sail.BitVec.extractLsb (rs2_val) (Functions.log2_xlen -i 1) 0))
  result


--purified
def execute_REMW_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)): BitVec 64 :=
  let rs1_val32 :=  (Sail.BitVec.extractLsb (rs1_val) 31 0)
  let rs2_val32 :=  (Sail.BitVec.extractLsb (rs2_val) 31 0)
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val32)
    else (BitVec.toNat rs1_val32)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val32)
    else (BitVec.toNat rs2_val32)
  let r : Int :=
    if (BEq.beq rs2_int 0)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  sign_extend (m := ((2 ^i 3) *i 8)) (to_bits 32 r) -- convert it to 32 bits and then sign extend it to 64

def execute_REM_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_int : Int :=
    if s -- checks sign
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let r : Int :=
    if (BEq.beq rs2_int 0) --checks if  mod zero or not
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (to_bits Functions.xlen r) -- converts it to xlen bits, usually 64

--purified
def execute_MULW_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := (Sail.BitVec.extractLsb rs1_val 31 0)
  let rs2_val32 := (Sail.BitVec.extractLsb rs2_val 31 0)
  let rs1_int : Int := (BitVec.toInt rs1_val32)
  let rs2_int : Int := (BitVec.toInt rs2_val32)
  let result32 := (Sail.BitVec.extractLsb (to_bits 64 (rs1_int *i rs2_int)) 31 0)
  let result : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) result32)
  result

--purified,
def execute_MUL_pure64 (mul_op : mul_op) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_int : Int :=
    if mul_op.signed_rs1 -- if signed then modell as integer operation
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if mul_op.signed_rs2
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let result_wide := (to_bits (2 *i Functions.xlen) (rs1_int *i rs2_int)) --adapt result vector width to 2^(exp1 + exp2)
  let result :=
    if mul_op.high -- if set return the higher xlen bits else the lower
    then (Sail.BitVec.extractLsb result_wide ((2 *i Functions.xlen) -i 1) Functions.xlen) --return either higher or lower xlen bits
    else (Sail.BitVec.extractLsb result_wide (Functions.xlen -i 1) 0)
  result


-- purified
def execute_DIVW_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb (rs1_val) 31 0
  let rs2_val32 :=  Sail.BitVec.extractLsb (rs2_val) 31 0
  let rs1_int : Int :=
    if s
    then (BitVec.toInt rs1_val32)
    else (BitVec.toNat rs1_val32)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val32)
    else (BitVec.toNat rs2_val32)
  let q : Int :=
    if (BEq.beq rs2_int 0)
    then (-1)
    else (Int.tdiv rs1_int rs2_int)
  let q' : Int :=
    if (Bool.and s (q >b ((2 ^i 31) -i 1)))
    then (0 -i (2 ^i 31))
    else q
  sign_extend (m := ((2 ^i 3) *i 8)) (to_bits 32 q')

def execute_DIV_pure64 (s : Bool) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let rs1_int : Int :=
    if s -- checks if signed division or not
    then (BitVec.toInt rs1_val)
    else (BitVec.toNat rs1_val)
  let rs2_int : Int :=
    if s
    then (BitVec.toInt rs2_val)
    else (BitVec.toNat rs2_val)
  let q : Int :=
    if (BEq.beq rs2_int 0) --checks wether its division by zero
    then (-1) -- no exception on division by zero, ATTENTION !
    else (Int.tdiv rs1_int rs2_int)
  let q' : Int :=
    if (Bool.and s (q >b xlen_max_signed)) -- in the overflow case we clamp the result to min_signed value
    then xlen_min_signed -- on overflow return smallest value but no exception ! ATTENTION
    else q
  (to_bits Functions.xlen q') -- return value


--purified immediate operations, did let the immediate be 12 bit vector
def execute_ITYPE_pure64 (imm : (BitVec 12)) (rs1_val : (BitVec 64)) (op : iop) : BitVec 64 :=
   let immext : xlenbits := (sign_extend (m := ((2 ^i 3) *i 8)) imm) -- sign extend immediate to 64 bits
    match op with -- result value will be returned instead of written into destination register
    | iop.RISCV_ADDI => rs1_val + immext --immediate addition
    | iop.RISCV_SLTI =>
          zero_extend (m := ((2 ^i 3) *i 8))
              (bool_to_bits (zopz0zI_s rs1_val immext)) --checks if immediate is strictly less than rs1_val and returns boolean as 64 bit sign extended result
    | iop.RISCV_SLTIU =>
          zero_extend (m := ((2 ^i 3) *i 8))
              (bool_to_bits (zopz0zI_u rs1_val immext))
    | iop.RISCV_ANDI =>  rs1_val &&& immext
    | iop.RISCV_ORI => rs1_val ||| immext
    | iop.RISCV_XORI => rs1_val ^^^ immext


-- purified
-- to do: ask if its valid to just match on op only and assume valid regs
def execute_ZICOND_RTYPE_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) (arg3 : zicondop) : BitVec 64 :=
  let merge_var := (rs2_val, rs1_val, arg3) -- original matches on reg number, we assuem valid register and match just on operation
  match merge_var with
  | ( _, _, zicondop.RISCV_CZERO_EQZ) =>
    let value := rs1_val
    let condition := rs2_val
    let result : xlenbits :=
      if (BEq.beq condition (zeros_implicit (n := ((2 ^i 3) *i 8))))
      then (zeros_implicit (n := ((2 ^i 3) *i 8)))
      else value
    result
  | (_, _, zicondop.RISCV_CZERO_NEZ) =>
    let value := rs1_val
    let condition :=  rs2_val
    let result : xlenbits := -- xlenbits is a 64 bit vector
      if (bne condition (zeros_implicit (n := ((2 ^i 3) *i 8))))
      then (zeros_implicit (n := ((2 ^i 3) *i 8)))
      else value
    result

def execute_ZBS_RTYPE_pure64 (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : brop_zbs) : BitVec 64 :=
  let mask : xlenbits :=
    (shift_bits_left (zero_extend (m := ((2 ^i 3) *i 8)) (0b1 : (BitVec 1)))
      (Sail.BitVec.extractLsb rs2_val 5 0))
  let result : xlenbits :=
    match op with
    | .RISCV_BCLR => (rs1_val &&& (Complement.complement mask))
    | .RISCV_BEXT =>
      (zero_extend (m := ((2 ^i 3) *i 8))
        (bool_to_bits (bne (rs1_val &&& mask) (zeros_implicit (n := ((2 ^i 3) *i 8))))))
    | .RISCV_BINV => (rs1_val ^^^ mask)
    | .RISCV_BSET => (rs1_val ||| mask)
  result

  def execute_ZBS_IOP_pure64 (shamt : (BitVec 6)) (rs1_val : BitVec 64) (op : biop_zbs) : BitVec 64 :=
  let mask : xlenbits :=
    (shift_bits_left (zero_extend (m := ((2 ^i 3) *i 8)) (0b1 : (BitVec 1))) shamt)
  let result : xlenbits :=
    match op with
    | .RISCV_BCLRI => (rs1_val &&& (Complement.complement mask))
    | .RISCV_BEXTI =>
      (zero_extend (m := ((2 ^i 3) *i 8))
        (bool_to_bits (bne (rs1_val &&& mask) (zeros_implicit (n := ((2 ^i 3) *i 8))))))
    | .RISCV_BINVI => (rs1_val ^^^ mask)
    | .RISCV_BSETI => (rs1_val ||| mask)
  result

-- to do didnt extract it to bit vec domain so far
def execute_ZBKB_RTYPE_pure64 (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : brop_zbkb) : BitVec 64 :=
    match op with
    | .RISCV_PACK =>
      ((Sail.BitVec.extractLsb rs2_val ((Functions.xlen_bytes *i 4) -i 1) 0) ++ (Sail.BitVec.extractLsb
          rs1_val ((Functions.xlen_bytes *i 4) -i 1) 0))
    | .RISCV_PACKH =>
      (zero_extend (m := ((2 ^i 3) *i 8))
        ((Sail.BitVec.extractLsb rs2_val 7 0) ++ (Sail.BitVec.extractLsb rs1_val 7 0)))

def execute_ZBB_RTYPEW_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) (op : bropw_zbb) : BitVec 64 :=
  let shamt := Sail.BitVec.extractLsb (rs2_val) 4 0
  let result : (BitVec 32) :=
    match op with
    | bropw_zbb.RISCV_ROLW => (rotate_bits_left rs1_val shamt)
    | bropw_zbb.RISCV_RORW => (rotate_bits_right rs1_val shamt)
  sign_extend (m := ((2 ^i 3) *i 8)) result

-- works one least significant bits and sign or zero extends them
def execute_ZBB_EXTOP_pure64 (rs1_val : BitVec 64) (op : extop_zbb) : BitVec 64 :=
    match op with
    | .RISCV_SEXTB => (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb rs1_val 7 0)) --sign extends a byte
    | .RISCV_SEXTH => (sign_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb rs1_val 15 0)) --sign extends halfword (16 bits)
    | .RISCV_ZEXTH => (zero_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb rs1_val 15 0)) --zero extends halfword (16 bits)


-- operations on unsigned words
def execute_ZBA_RTYPEUW_pure64 (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : bropw_zba) : BitVec 64 :=
  let shamt : (BitVec 2) :=
    match op with
    | .RISCV_ADDUW => (0b00 : (BitVec 2)) -- add unsigned word
    | .RISCV_SH1ADDUW => (0b01 : (BitVec 2))  --shift unsigned word left by 1 and add
    | .RISCV_SH2ADDUW => (0b10 : (BitVec 2)) -- shift unsigned word left by 1 and add
    | .RISCV_SH3ADDUW => (0b11 : (BitVec 2)) -- shift unsigned word left by 1 and add
  let result : xlenbits :=
    ((shift_bits_left (zero_extend (m := ((2 ^i 3) *i 8)) (Sail.BitVec.extractLsb rs1_val 31 0))
        shamt) + rs2_val) -- left shift by shamt and then add
  result

def execute_ZBA_RTYPE_pure64 (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : brop_zba) : BitVec 64 :=
  let shamt : (BitVec 2) :=
    match op with
    | .RISCV_SH1ADD => (0b01 : (BitVec 2))
    | .RISCV_SH2ADD => (0b10 : (BitVec 2))
    | .RISCV_SH3ADD => (0b11 : (BitVec 2))
  let result : xlenbits := ((shift_bits_left rs1_val shamt) + rs2_val)
  result


def execute_ZBB_RTYPE_pure (rs2_val : BitVec 64) (rs1_val : BitVec 64) (op : brop_zbb) : BitVec 64 :=
   let result : xlenbits :=
    match op with
    | .RISCV_ANDN => (rs1_val &&& (Complement.complement rs2_val))
    | .RISCV_ORN => (rs1_val ||| (Complement.complement rs2_val))
    | .RISCV_XNOR => (Complement.complement (rs1_val ^^^ rs2_val))
    | .RISCV_MAX => (to_bits 64 (Max.max (BitVec.toInt rs1_val) (BitVec.toInt rs2_val)))
    | .RISCV_MAXU => (to_bits 64 (Max.max (BitVec.toNat rs1_val) (BitVec.toNat rs2_val)))
    | .RISCV_MIN => (to_bits 64 (Min.min (BitVec.toInt rs1_val) (BitVec.toInt rs2_val)))
    | .RISCV_MINU => (to_bits 64 (Min.min (BitVec.toNat rs1_val) (BitVec.toNat rs2_val)))
    | .RISCV_ROL => (rotate_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 5 0))
    | .RISCV_ROR => (rotate_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 5 0))
  result



end PureFunctions

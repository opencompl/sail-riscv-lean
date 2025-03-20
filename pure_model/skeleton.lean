import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
-- added the imports bellow, had to move pure_func to the library folder
import LeanRV64DLEAN
import LeanRV64DLEAN.pure_func

set_option maxRecDepth 10_000
set_option maxHeartbeats 1_000_000_000
set_option match.ignoreUnusedAlts true

open Functions
open Retired
open Sail
open PureFunctions

--example execute_MUL rs2 rs1 rd mul_op  = skeleton2 rs2 rs1 (fun val1 val2 => execute_MUL_pure val1 val2 mulop ) := by

  /- def skeleton (rs2 : BitVec 5) (rs1 : BitVec 5) (rd : BitVec 5) (op : BitVec 32 → BitVec 32 → BitVec 32) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := op rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS -/

 -- regidx is of type BitVec
def skeleton_binary  (rs2 : regidx) (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := execute_func rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_unary (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let result := execute_func rs1_val
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_UTYPE  (imm : BitVec 20) (rd : regidx) (op : uop) (execute_func : BitVec 20 → BitVec 64 → uop → BitVec 64) : SailM Retired := do
  let pc ← get_arch_pc () -- states that I modelled this model like this bc its more uniform and neat but made the proof more compilcated
  let result := execute_func imm pc op
  wX_bits rd result
  pure RETIRE_SUCCESS

-- introduced more skeletons depeending on whether pc was used or not

def skeleton_UTYPE_AUIPC  (imm : BitVec 20) (rd : regidx) (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM Retired := do
  let pc ← get_arch_pc (); -- TO DO READ IN THE PC , think of the effects
  let result := execute_func imm pc
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_UTYPE_LUI  (imm : BitVec 20) (rd : regidx) (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM Retired := do
  let result := execute_func imm 0#64
  wX_bits rd result
  pure RETIRE_SUCCESS


theorem add_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ADDIW (imm) (rs1) (rd)
    = skeleton_unary rs1 rd (execute_ADDIW_pure64 imm)
  := by
  unfold Functions.execute_ADDIW skeleton_unary execute_ADDIW_pure64
  rfl

-- case destinction on the type of uop operation
theorem utype_eq_LUI (imm : (BitVec 20)) (rd : regidx):
    Functions.execute_UTYPE imm rd (uop.RISCV_LUI)
    =
    skeleton_UTYPE_LUI imm rd (fun imm pc => execute_UTYPE_pure64 imm pc (uop.RISCV_LUI) )
  := by
  unfold Functions.execute_UTYPE skeleton_UTYPE_LUI execute_UTYPE_pure64
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp, pure_bind]

theorem utype_eq_AUIPC (imm : (BitVec 20)) (rd : regidx):
  Functions.execute_UTYPE imm rd (uop.RISCV_AUIPC)
    = skeleton_UTYPE_AUIPC  imm rd (fun imm pc => execute_UTYPE_pure64 imm pc uop.RISCV_AUIPC)
  := by
    unfold Functions.execute_UTYPE skeleton_UTYPE_AUIPC execute_UTYPE_pure64
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp,
      bind_map_left, BitVec.add_eq]

/-
theorem ignore_pc (x: SailM (BitVec 64)) :
  let pc ← get_arch_pc ();
  (fun a => RETIRE_SUCCESS) <$> wX_bits rd (sign_extend ((imm : (BitVec 20))  ++ 0#12)) =
  (fun a => RETIRE_SUCCESS) <$> wX_bits rd (sign_extend ((imm : (BitVec 20)) ++ 0#12)) :=
    by simp
-/
--#print StateT
--#check (Functions.execute_UTYPE ?imm ?rd ?f : _ → _)

--def SailM := Nat → Nat

--def f : NatFun :=
  --fun a => a
--(h: Register.PC = Some s ) (h: Register.PC == Some s )

theorem utype_eq (imm : (BitVec 20)) (rd : regidx) (op : uop) (h_pc : s.regs.get? Register.PC = some valt):
    Functions.execute_UTYPE imm rd op s
     = skeleton_UTYPE imm rd op (execute_UTYPE_pure64) s
  := by
  unfold Functions.execute_UTYPE skeleton_UTYPE execute_UTYPE_pure64
  cases op
  ·
    simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp, pure_bind, Nat.reducePow,
      Nat.reduceMul]
    simp [get_arch_pc, readReg, PreSail.readReg, Monad.toBind, EStateM.instMonad, EStateM.map,
      EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
    cases hs : s.regs.get? Register.PC
    · rw [hs] at h_pc
      contradiction
    · simp only
      rfl
  ·
   simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp,
     bind_map_left, BitVec.add_eq]

theorem shiftiwop_eq (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) :
    Functions.execute_SHIFTIWOP (shamt) (rs1) (rd) (op)
      = skeleton_unary rs1 rd (fun val1 => PureFunctions.execute_SHIFTIWOP_pure64 shamt op val1)
  := by
  unfold Functions.execute_SHIFTIWOP skeleton_unary execute_SHIFTIWOP_pure64
  rfl

theorem shiftiop_eq (shamt : (BitVec 6)) (op : sop) (rs1 : regidx) (rd : regidx) :
    Functions.execute_SHIFTIOP (shamt) (rs1) (rd) (op)
      = skeleton_unary rs1 rd (fun val1 => PureFunctions.execute_SHIFTIOP_pure64 shamt op val1)
  := by
  unfold Functions.execute_SHIFTIOP skeleton_unary execute_SHIFTIOP_pure64
  cases op
  <;> simp

theorem rtypew_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) :
    Functions.execute_RTYPEW (rs2) (rs1) (rd) (op)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_RTYPEW_pure64 op val2 val1)
  := by -- attention_ ordering of arguements
  unfold Functions.execute_RTYPEW skeleton_binary execute_RTYPEW_pure64
  rfl

theorem rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (op)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_RTYPE_pure64 op val2 val1)
  := by
  unfold Functions.execute_RTYPE skeleton_binary execute_RTYPE_pure64
  simp
  cases op
  <;> simp


theorem remw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_REMW (rs2) (rs1) (rd) (s)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_REMW_pure64 s val2 val1)
  := by
  unfold Functions.execute_REMW skeleton_binary execute_REMW_pure64
  rfl

theorem rem_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_REM (rs2) (rs1) (rd) (s)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_REM_pure64 s val2 val1)
  := by
  unfold Functions.execute_REM skeleton_binary execute_REM_pure64
  rfl

theorem mulw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MULW (rs2) (rs1) (rd)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_MULW_pure64 val2 val1)
  := by
  unfold Functions.execute_MULW skeleton_binary execute_MULW_pure64
  rfl

theorem mul_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_MUL_pure64 mul_op val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary execute_MUL_pure64
  rfl

theorem divw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_DIVW (rs2 ) (rs1) (rd) (s)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_DIVW_pure64 s val2 val1)
  := by
  unfold Functions.execute_DIVW skeleton_binary execute_DIVW_pure64
  rfl


theorem div_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (s : Bool) :
    Functions.execute_DIV (rs2) (rs1) (rd) (s)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_DIV_pure64 s val2 val1)
  := by
  unfold Functions.execute_DIV skeleton_binary execute_DIV_pure64
  rfl

theorem itype_eq (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (op)
      = skeleton_unary rs1 rd (fun val1 => execute_ITYPE_pure64 imm val1 op)
  := by
  unfold Functions.execute_ITYPE skeleton_unary execute_ITYPE_pure64
  · cases op
  <;> simp

theorem zicond_rtype_eq (arg0 : regidx) (arg1 : regidx) (arg2 : regidx) (arg3 : zicondop) :
    Functions.execute_ZICOND_RTYPE arg0 arg1 arg2 arg3
      = skeleton_binary arg0 arg1 arg2 (fun val1 val2 => execute_ZICOND_RTYPE_pure64 val2 val1 arg3)
  := by
  unfold Functions.execute_ZICOND_RTYPE skeleton_binary execute_ZICOND_RTYPE_pure64
  · cases arg3
  <;> simp

theorem zbs_rytpe_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zbs) :
    Functions.execute_ZBS_RTYPE rs2 rs1 rd op
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_ZBS_RTYPE_pure64 val2 val1 op)
  := by
  unfold Functions.execute_ZBS_RTYPE skeleton_binary execute_ZBS_RTYPE_pure64
  rfl

theorem zbs_iop_eq (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : biop_zbs) :
    execute_ZBS_IOP (shamt ) (rs1) (rd) (op) = skeleton_unary rs1 rd (fun val1 => execute_ZBS_IOP_pure64 shamt val1 op)
  := by
  unfold Functions.execute_ZBS_IOP skeleton_unary execute_ZBS_IOP_pure64
  rfl

-- to do ZBKS for crypto

theorem zbb_rtypew_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : bropw_zbb) :
    Functions.execute_ZBB_RTYPEW (rs2) (rs1) (rd) (op)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_ZBB_RTYPEW_pure64 val2 val1 op)
  := by
  unfold Functions.execute_ZBB_RTYPEW skeleton_binary execute_ZBB_RTYPEW_pure64
  rfl


theorem zbb_extop_eq (rs1 : regidx) (rd : regidx) (op : extop_zbb)  :
    Functions.execute_ZBB_EXTOP (rs1) (rd) (op)
    = skeleton_unary rs1 rd (fun val1 => execute_ZBB_EXTOP_pure64 val1 op)
  := by
  unfold Functions.execute_ZBB_EXTOP skeleton_unary execute_ZBB_EXTOP_pure64
  rfl

theorem zba_rtypeuw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : bropw_zba)  :
    Functions.execute_ZBA_RTYPEUW (rs2) (rs1) (rd) (op)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_ZBA_RTYPEUW_pure64 val2 val1 op)
  := by
  unfold Functions.execute_ZBA_RTYPEUW skeleton_binary execute_ZBA_RTYPEUW_pure64
  rfl

theorem zba_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zba)  :
    Functions.execute_ZBA_RTYPE (rs2) (rs1) (rd) (op)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_ZBA_RTYPE_pure64 val2 val1 op)
  := by
  unfold Functions.execute_ZBA_RTYPE skeleton_binary execute_ZBA_RTYPE_pure64
  rfl


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp



--example proof attempt
/-example :
  execute_ZBB_RTYPEW rs2 rs1 rd op = skeleton rs2 rs1 rd (execute_ZBB_RTYPEW_pure32):= by
  sorry --[TO DO ]

from pairing with alex
--theorem rX_bits_eq (rX : BitVec 5) : rX_bits rX = regval_from_reg <$> _ := by -- (readReg <| Register.ofBitVec rX) := by
  --simp [rX_bits, Functions.rX]


example execute_MUL rs2 rs1 rd mul_op  = skeleton2 rs2 rs1 (fun val1 val2 => execute_MUL_pure val1 val2 mulop ) := by
  sorry

example executeADD rs2 rs1 rd addOP = skeleton2 rs2 rs1 (λ val1 val2 . executeAddPure val1 val2 addOp)

-/

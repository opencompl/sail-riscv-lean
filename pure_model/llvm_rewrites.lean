-- modelling and verfying RISC-V rewrites from the LLVM backend
/- writting them as a sequence of my pure functions:
  1.) choose an eexample and rewrite it
  2.) write a mapping that takes in RISC-V code and transaltes each instruction
  into an application of my execution function and omits a sequence of bit vecotrs
  3.) proof the rewrites using bv_decide and other lean features
-/

/- simple RISC-V assembly code:


addiw a0, a0, 1
ret

lowered to bit vec operations:

would be modelled as bit vector := by
  rw [add_eq 1#12 a0 a0]
  rw [execute_ADDIW_pure64]
  rw [xecute_ADDIW_pure64_BitVec]


  BitVec.signExtend 64
     (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val))
-/

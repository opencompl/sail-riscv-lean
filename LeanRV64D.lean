import LeanRV64D.Flow
import LeanRV64D.Common
import LeanRV64D.Prelude
import LeanRV64D.Xlen
import LeanRV64D.RvfiDii
import LeanRV64D.PlatformConfig
import LeanRV64D.Regs
import LeanRV64D.SysRegs
import LeanRV64D.InterruptRegs
import LeanRV64D.PmpRegs
import LeanRV64D.FdextRegs
import LeanRV64D.VextRegs
import LeanRV64D.Smcntrpmf
import LeanRV64D.ZicfilpRegs
import LeanRV64D.SysControl
import LeanRV64D.Platform
import LeanRV64D.Pma
import LeanRV64D.VmemTlb
import LeanRV64D.Vmem
import LeanRV64D.ZicsrInsts
import LeanRV64D.Zihpm
import LeanRV64D.Ssqosid
import LeanRV64D.Step
import LeanRV64D.Main

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

noncomputable section
namespace LeanRV64D

open ConcurrencyInterfaceV1

namespace Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zvabd_vwabda_func6
open zvabd_vabd_func6
open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vstart_class
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open stateen_bit
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open page_based_mem_type
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_exception
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open cacheop
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
open biop
open barrier_kind
open amoop
open agtype
open XtvecModeReservedBehavior
open XipReadType
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Splittability
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privileged_ISA_Version
open Privilege
open PointerMaskingMode
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open PM_Ext
open OOBVstartReservedBehavior
open MemoryRegionType
open MemoryAccessType
open InterruptType
open IllegalVtypeReservedBehavior
open ISA_Format
open HartState
open FflagsDirtyPolicy
open FetchResult
open FetchBytes_Result
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open CSRCheckResult
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg rvfi_instruction (← (undefined_RVFI_DII_Instruction_Packet ()))
  writeReg rvfi_inst_data (← (undefined_RVFI_DII_Execution_Packet_InstMetaData ()))
  writeReg rvfi_pc_data (← (undefined_RVFI_DII_Execution_Packet_PC ()))
  writeReg rvfi_int_data (← (undefined_RVFI_DII_Execution_Packet_Ext_Integer ()))
  writeReg rvfi_int_data_present (← (undefined_bool ()))
  writeReg rvfi_mem_data (← (undefined_RVFI_DII_Execution_Packet_Ext_MemAccess ()))
  writeReg rvfi_mem_data_present (← (undefined_bool ()))
  writeReg PC (← (undefined_bitvector 64))
  writeReg nextPC (← (undefined_bitvector 64))
  writeReg x1 (← (undefined_bitvector 64))
  writeReg x2 (← (undefined_bitvector 64))
  writeReg x3 (← (undefined_bitvector 64))
  writeReg x4 (← (undefined_bitvector 64))
  writeReg x5 (← (undefined_bitvector 64))
  writeReg x6 (← (undefined_bitvector 64))
  writeReg x7 (← (undefined_bitvector 64))
  writeReg x8 (← (undefined_bitvector 64))
  writeReg x9 (← (undefined_bitvector 64))
  writeReg x10 (← (undefined_bitvector 64))
  writeReg x11 (← (undefined_bitvector 64))
  writeReg x12 (← (undefined_bitvector 64))
  writeReg x13 (← (undefined_bitvector 64))
  writeReg x14 (← (undefined_bitvector 64))
  writeReg x15 (← (undefined_bitvector 64))
  writeReg x16 (← (undefined_bitvector 64))
  writeReg x17 (← (undefined_bitvector 64))
  writeReg x18 (← (undefined_bitvector 64))
  writeReg x19 (← (undefined_bitvector 64))
  writeReg x20 (← (undefined_bitvector 64))
  writeReg x21 (← (undefined_bitvector 64))
  writeReg x22 (← (undefined_bitvector 64))
  writeReg x23 (← (undefined_bitvector 64))
  writeReg x24 (← (undefined_bitvector 64))
  writeReg x25 (← (undefined_bitvector 64))
  writeReg x26 (← (undefined_bitvector 64))
  writeReg x27 (← (undefined_bitvector 64))
  writeReg x28 (← (undefined_bitvector 64))
  writeReg x29 (← (undefined_bitvector 64))
  writeReg x30 (← (undefined_bitvector 64))
  writeReg x31 (← (undefined_bitvector 64))
  writeReg cur_privilege (← (undefined_Privilege ()))
  writeReg cur_inst (← (undefined_bitvector 64))
  writeReg mtvec (← (undefined_Mtvec ()))
  writeReg mcause (← (undefined_Mcause ()))
  writeReg mepc (← (undefined_bitvector 64))
  writeReg mtval (← (undefined_bitvector 64))
  writeReg mscratch (← (undefined_bitvector 64))
  writeReg scounteren (← (undefined_Counteren ()))
  writeReg mcounteren (← (undefined_Counteren ()))
  writeReg mcountinhibit (← (undefined_Counterin ()))
  writeReg mcycle (← (undefined_bitvector 64))
  writeReg mtime (← (undefined_bitvector 64))
  writeReg minstret (← (undefined_bitvector 64))
  writeReg minstret_increment (← (undefined_bool ()))
  writeReg stvec (← (undefined_Mtvec ()))
  writeReg sscratch (← (undefined_bitvector 64))
  writeReg sepc (← (undefined_bitvector 64))
  writeReg scause (← (undefined_Mcause ()))
  writeReg stval (← (undefined_bitvector 64))
  writeReg tselect (← (undefined_bitvector 64))
  writeReg mie (← (undefined_Minterrupts ()))
  writeReg mip (← (undefined_Minterrupts ()))
  writeReg medeleg (← (undefined_Medeleg ()))
  writeReg mideleg (← (undefined_Minterrupts ()))
  writeReg pmpcfg_n (← (undefined_vector 64 (← (undefined_Pmpcfg_ent ()))))
  writeReg pmpaddr_n (← (undefined_vector 64 (← (undefined_bitvector 64))))
  writeReg f0 (← (undefined_bitvector (8 *i 8)))
  writeReg f1 (← (undefined_bitvector (8 *i 8)))
  writeReg f2 (← (undefined_bitvector (8 *i 8)))
  writeReg f3 (← (undefined_bitvector (8 *i 8)))
  writeReg f4 (← (undefined_bitvector (8 *i 8)))
  writeReg f5 (← (undefined_bitvector (8 *i 8)))
  writeReg f6 (← (undefined_bitvector (8 *i 8)))
  writeReg f7 (← (undefined_bitvector (8 *i 8)))
  writeReg f8 (← (undefined_bitvector (8 *i 8)))
  writeReg f9 (← (undefined_bitvector (8 *i 8)))
  writeReg f10 (← (undefined_bitvector (8 *i 8)))
  writeReg f11 (← (undefined_bitvector (8 *i 8)))
  writeReg f12 (← (undefined_bitvector (8 *i 8)))
  writeReg f13 (← (undefined_bitvector (8 *i 8)))
  writeReg f14 (← (undefined_bitvector (8 *i 8)))
  writeReg f15 (← (undefined_bitvector (8 *i 8)))
  writeReg f16 (← (undefined_bitvector (8 *i 8)))
  writeReg f17 (← (undefined_bitvector (8 *i 8)))
  writeReg f18 (← (undefined_bitvector (8 *i 8)))
  writeReg f19 (← (undefined_bitvector (8 *i 8)))
  writeReg f20 (← (undefined_bitvector (8 *i 8)))
  writeReg f21 (← (undefined_bitvector (8 *i 8)))
  writeReg f22 (← (undefined_bitvector (8 *i 8)))
  writeReg f23 (← (undefined_bitvector (8 *i 8)))
  writeReg f24 (← (undefined_bitvector (8 *i 8)))
  writeReg f25 (← (undefined_bitvector (8 *i 8)))
  writeReg f26 (← (undefined_bitvector (8 *i 8)))
  writeReg f27 (← (undefined_bitvector (8 *i 8)))
  writeReg f28 (← (undefined_bitvector (8 *i 8)))
  writeReg f29 (← (undefined_bitvector (8 *i 8)))
  writeReg f30 (← (undefined_bitvector (8 *i 8)))
  writeReg f31 (← (undefined_bitvector (8 *i 8)))
  writeReg fcsr (← (undefined_Fcsr ()))
  writeReg vr0 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr1 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr2 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr3 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr4 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr5 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr6 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr7 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr8 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr9 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr10 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr11 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr12 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr13 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr14 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr15 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr16 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr17 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr18 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr19 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr20 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr21 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr22 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr23 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr24 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr25 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr26 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr27 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr28 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr29 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr30 (← (undefined_bitvector (2 ^i 8)))
  writeReg vr31 (← (undefined_bitvector (2 ^i 8)))
  writeReg vstart (← (undefined_bitvector 64))
  writeReg vl (← (undefined_bitvector 64))
  writeReg vtype (← (undefined_Vtype ()))
  writeReg vcsr (← (undefined_Vcsr ()))
  writeReg mcyclecfg (← (undefined_CountSmcntrpmf ()))
  writeReg minstretcfg (← (undefined_CountSmcntrpmf ()))
  writeReg elp (← (undefined_bitvector 1))
  writeReg mtimecmp (← (undefined_bitvector 64))
  writeReg stimecmp (← (undefined_bitvector 64))
  writeReg satp (← (undefined_bitvector 64))
  writeReg mhpmevent (← (undefined_vector 32 (← (undefined_HpmEvent ()))))
  writeReg mhpmcounter (← (undefined_vector 32 (← (undefined_bitvector 64))))
  writeReg srmcfg (← (undefined_Srmcfg ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg fp_rounding_global fp_rounding_default
  writeReg misa (_update_Misa_MXL (Mk_Misa (zeros (n := 64))) (architecture_bits_forwards RV64))
  writeReg mstatus (let mxl := (architecture_bits_forwards RV64)
  (_update_Mstatus_UXL
    (_update_Mstatus_SXL (Mk_Mstatus (zeros (n := 64)))
      (if (((xlen != 32) && (hartSupports Ext_S)) : Bool)
      then mxl
      else (zeros (n := 2))))
    (if (((xlen != 32) && (hartSupports Ext_U)) : Bool)
    then mxl
    else (zeros (n := 2)))))
  writeReg hstateen0 (Mk_Hstateen0 (zeros (n := 64)))
  writeReg hstateen1 (Mk_Hstateen1 (zeros (n := 64)))
  writeReg hstateen2 (Mk_Hstateen2 (zeros (n := 64)))
  writeReg hstateen3 (Mk_Hstateen3 (zeros (n := 64)))
  writeReg mstateen0 (Mk_Mstateen0 (zeros (n := 64)))
  writeReg mstateen1 (Mk_Mstateen1 (zeros (n := 64)))
  writeReg mstateen2 (Mk_Mstateen2 (zeros (n := 64)))
  writeReg mstateen3 (Mk_Mstateen3 (zeros (n := 64)))
  writeReg sstateen0 (Mk_Sstateen0 (zeros (n := 32)))
  writeReg sstateen1 (Mk_Sstateen1 (zeros (n := 32)))
  writeReg sstateen2 (Mk_Sstateen2 (zeros (n := 32)))
  writeReg sstateen3 (Mk_Sstateen3 (zeros (n := 32)))
  writeReg senvcfg (← (legalize_senvcfg (Mk_SEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg mseccfg (← (legalize_mseccfg (Mk_Seccfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg menvcfg (← (legalize_menvcfg (Mk_MEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg mvendorid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg mimpid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg marchid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg mhartid (← (to_bits_checked (l := 64) (0 : Int)))
  writeReg mconfigptr (zeros (n := 64))
  writeReg sig_meip 0#1
  writeReg sig_seip 0#1
  writeReg pc_reset_address (zeros (n := 64))
  writeReg htif_tohost_base none
  writeReg htif_tohost (zeros (n := 64))
  writeReg htif_done false
  writeReg htif_exit_code (zeros (n := 64))
  writeReg htif_cmd_write (zeros (n := 1))
  writeReg htif_payload_writes (zeros (n := 4))
  writeReg pma_regions [{ base := 0b0000000000000000000000000000000000000000000000000001000000000000#64
                          size := 0b0000000000000000000000000000000000000000000000000001000000000000#64
                          attributes := { mem_type := IOMemory
                                          cacheable := true
                                          coherent := false
                                          executable := false
                                          readable := true
                                          writable := false
                                          read_idempotent := true
                                          write_idempotent := true
                                          misaligned_exceptions := { load_store := none
                                                                     vector := none
                                                                     amo := AccessFault }
                                          atomic_support := AMONone
                                          reservability := RsrvNone
                                          supports_cbo_zero := false
                                          supports_pte_read := false
                                          supports_pte_write := false
                                          misaligned_atomicity_granule_size_exp := 0
                                          vector_misaligned_atomicity_granule_size_exp := 0 }
                          include_in_device_tree := false }, { base := 0b0000000000000000000000000000000000000010000000000000000000000000#64
                                                               size := 0b0000000000000000000000000000000000010000000000000000000000000000#64
                                                               attributes := { mem_type := IOMemory
                                                                               cacheable := false
                                                                               coherent := true
                                                                               executable := false
                                                                               readable := true
                                                                               writable := true
                                                                               read_idempotent := false
                                                                               write_idempotent := false
                                                                               misaligned_exceptions := { load_store := none
                                                                                                          vector := none
                                                                                                          amo := AccessFault }
                                                                               atomic_support := AMONone
                                                                               reservability := RsrvNone
                                                                               supports_cbo_zero := false
                                                                               supports_pte_read := false
                                                                               supports_pte_write := false
                                                                               misaligned_atomicity_granule_size_exp := 0
                                                                               vector_misaligned_atomicity_granule_size_exp := 0 }
                                                               include_in_device_tree := false }, { base := 0b0000000000000000000000000000000010000000000000000000000000000000#64
                                                                                                    size := 0b0000000000000000000000000000000010000000000000000000000000000000#64
                                                                                                    attributes := { mem_type := MainMemory
                                                                                                                    cacheable := true
                                                                                                                    coherent := true
                                                                                                                    executable := true
                                                                                                                    readable := true
                                                                                                                    writable := true
                                                                                                                    read_idempotent := true
                                                                                                                    write_idempotent := true
                                                                                                                    misaligned_exceptions := { load_store := none
                                                                                                                                               vector := none
                                                                                                                                               amo := AccessFault }
                                                                                                                    atomic_support := AMOCASQ
                                                                                                                    reservability := RsrvEventual
                                                                                                                    supports_cbo_zero := true
                                                                                                                    supports_pte_read := true
                                                                                                                    supports_pte_write := true
                                                                                                                    misaligned_atomicity_granule_size_exp := 4
                                                                                                                    vector_misaligned_atomicity_granule_size_exp := 4 }
                                                                                                    include_in_device_tree := true }]
  writeReg tlb (vectorInit none)
  writeReg ssp (zeros (n := 64))
  writeReg hart_state (HART_ACTIVE ())
  (initialize_registers ())

end LeanRV64D.Functions

open LeanRV64D
open LeanRV64D.Functions

def main (_ : List String) : IO UInt32 := do
  main_of_sail_main ⟨default, (), default, default, default, default⟩ (sail_model_init >=> sail_main)

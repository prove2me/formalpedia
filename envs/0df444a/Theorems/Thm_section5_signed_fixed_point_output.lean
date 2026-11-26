-- Prove2me | Theorems.Thm_section5_signed_fixed_point_output
-- name    : section5_signed_fixed_point_output
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:51.747081+00:00
-- url     : https://prove2.me/theorems/b375c38c-6d4e-58ee-b31f-649d1f086324
-- title:
--   Exact sign-dependent fixed-point decoding
-- statement:
--   Let z be an (a+1)-bit offset-binary fixed-point word with fractional precision f, and b a Boolean sign. Decode the source's signed-output integer in a+2 bits after converting its little-endian representation to the public most-significant-bit convention. Its real value is exactly $$\operatorname{fp}_{a+2,f}(\operatorname{signedOutput}(z,b))=(-1)^b\operatorname{fp}_{a+1,f}(z).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SignedFixedPointOutput.lean, lines 38–41.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_signed_fixed_point_output (a f : ℕ) (z : Qubits (a+1)) (flip : Bool) :
    fpVal (a+2) f
      (section5_lsb_to_msb (natToBitsLSB (a+2) (section5_signed_output_integer a (bitsToNat z) flip)))=
        if flip then -fpVal (a+1) f z else fpVal (a+1) f z := by sorry

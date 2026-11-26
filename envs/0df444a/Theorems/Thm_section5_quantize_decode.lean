-- Prove2me | Theorems.Thm_section5_quantize_decode
-- name    : section5_quantize_decode
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:02.507431+00:00
-- url     : https://prove2.me/theorems/0639fa07-fd40-43f8-83e6-663bda06b0ed
-- title:
--   Exact decoding of floor-quantized fixed-point coordinates
-- statement:
--   Let $f\ge0$ be a natural number and $x\in\mathbb R$ satisfy $|x|\le1$. Encode the nonnegative integer $N=2^{f+1}+\lfloor2^f x\rfloor$ as an $(f+2)$-bit most-significant-bit-first string. Decode a string of unsigned value $N$ by the offset-binary rule $(N-2^{f+1})/2^f$. Then
--
--   $$
--   \operatorname{decode}_f(\operatorname{quantize}_f(x))=\frac{\lfloor2^f x\rfloor}{2^f}.
--   $$
--
--   This establishes the exact real value represented by the fixed-point quantization.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5FixedPointQuantization.lean, section5_quantize_decode, lines 39–52.

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
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_quantize_decode (f : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    fpVal (f+2) f (section5_quantize_bits f x)=((⌊(2:ℝ)^f*x⌋:ℤ):ℝ)/(2:ℝ)^f := by sorry

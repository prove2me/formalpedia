-- Prove2me | Theorems.Thm_section5_dyadic_floor
-- name    : section5_dyadic_floor
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:10:15.090663+00:00
-- url     : https://prove2.me/theorems/c6c5dc5f-894e-4d8e-86c6-15e1bc392082
-- title:
--   Dyadic scaling and integer division
-- statement:
--   For natural numbers $f\le S$ and any integer $v$,
--
--   $$\left\lfloor2^f\,2^{-S}v\right\rfloor=v\mathbin{\mathrm{div}}2^{S-f}.$$
--
--   Here division on the right is Euclidean integer division, so the equality includes negative inputs. This relates dyadic quantization to integer bit extraction.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5DyadicVectorOutput.lean, lines 12–22.

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
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_dyadic_floor (S f : ℕ) (hf : f ≤ S) (v : ℤ) :
    ⌊(2:ℝ)^f*(((2:ℝ)^S)⁻¹*(v:ℝ))⌋=v/(2:ℤ)^(S-f) := by sorry

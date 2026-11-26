-- Prove2me | Theorems.Thm_section5_decoder_parameters_polynomial
-- name    : section5_decoder_parameters_polynomial
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:47.559359+00:00
-- url     : https://prove2.me/theorems/3dfcfe87-5fef-441b-bc0c-b3e0d65338c5
-- title:
--   Polynomial bounds on decoder parameters
-- statement:
--   Let n≥1 and 0<ε<1. For the source's explicit iteration count k, fractional precision f and signed integer width b at parameters (n,ε), $$k\le801n/\varepsilon,\qquad f\le1750(n/\varepsilon)^2,\qquad b\le2000000(n/\varepsilon)^3.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicDecoderParameters.lean, lines 60–64.

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
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
set_option autoImplicit false

theorem section5_decoder_parameters_polynomial (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (section5_decoder_iterations n ε:ℝ) ≤ 801*(n/ε) ∧
      (section5_decoder_fraction_bits n ε:ℝ) ≤ 1750*(n/ε)^2 ∧
      (section5_decoder_integer_width n ε:ℝ) ≤ 2000000*(n/ε)^3 := by sorry

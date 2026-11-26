-- Prove2me | Theorems.Thm_section5_middle_window_scales
-- name    : section5_middle_window_scales
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:55.386984+00:00
-- url     : https://prove2.me/theorems/5ce96704-354d-45a5-b28b-d8412a4dca3f
-- title:
--   Scales of a middle-bit window
-- statement:
--   Let q,B be natural numbers with 2B+6≤q; put s=⌊q/2⌋−B, b=2B+2 and δ=√(4π/2^q). Then $$s+b\le q-1,\quad2\le\delta2^{s+B}\le4,\quad\delta2^{b-1+s}-\delta\ge2^B,\quad\delta(2^s+2)2^B\le12.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WindowParameters.lean, lines 32–39.

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Mathlib
set_option autoImplicit false
open QuantumLTF.Example

theorem section5_middle_window_scales (q B : ℕ) (hq : 2*B+6 ≤ q) :
    let s := q/2-B
    let b := 2*B+2
    s+b ≤ q-1 ∧
      2 ≤ gridSpacing (2^q)*(2:ℝ)^s*(2:ℝ)^B ∧
      gridSpacing (2^q)*(2:ℝ)^s*(2:ℝ)^B ≤ 4 ∧
      gridSpacing (2^q)*(2:ℝ)^(b-1)*(2:ℝ)^s-gridSpacing (2^q) ≥ (2:ℝ)^B ∧
      gridSpacing (2^q)*((2:ℝ)^s+2)*(2:ℝ)^B ≤ 12 := by sorry

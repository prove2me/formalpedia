-- Prove2me | Theorems.Thm_section5_rational_fp_relative_error
-- name    : section5_rational_fp_relative_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:37.911798+00:00
-- url     : https://prove2.me/theorems/f7858d46-404a-561e-bb76-cc8042d14a2a
-- title:
--   Relative direction error of rational fixed-point output
-- statement:
--   Let n≥1, 0<ε<1, b>0 and 2^f≥48n/(bε). Let r∈Q^n have |r_i|≤1 and Euclidean norm at least b. Let o be the real vector obtained by decoding its source-defined (f+2)-bit fixed-point encoding at fractional precision f. Then $$o\ne0,\qquad\|o/\|o\|-r/\|r\|\|\le\varepsilon/24.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RationalFixedPoint.lean, lines 34–42.

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
import Definitions.Def_Section5Verified_Section5RationalFixedPoint
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
import Theorems.Thm_section5_quantize_relative_error
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_rational_fp_relative_error {n : ℕ} (hn : 1 ≤ n) (f : ℕ)
    (ε b : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hb : 0 < b)
    (hprec : 48*(n:ℝ)/(b*ε) ≤ (2:ℝ)^f)
    (r : Fin n → ℚ) (hr : ∀ i, |(r i:ℝ)| ≤ 1)
    (hnorm : b ≤ ‖WithLp.toLp 2 (fun i => (r i:ℝ))‖) :
    let out : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => fpVal (f+2) f (section5_rational_fp_vector f r i))
    out ≠ 0 ∧ ‖NormedSpace.normalize out-
      NormedSpace.normalize (WithLp.toLp 2 (fun i => (r i:ℝ)))‖ ≤ ε/24 := by sorry

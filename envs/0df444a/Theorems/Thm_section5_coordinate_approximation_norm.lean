-- Prove2me | Theorems.Thm_section5_coordinate_approximation_norm
-- name    : section5_coordinate_approximation_norm
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:32.078394+00:00
-- url     : https://prove2.me/theorems/5a9674a9-7816-4b2e-ad97-ef62cdd685d5
-- title:
--   Euclidean norm from coordinatewise approximation
-- statement:
--   Let x,y∈R^n and δ≥0. If |x_i−y_i|≤δ for every coordinate i, then $$\|x-y\|_2\le\delta\sqrt n.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5WindowLabelProbability.lean, lines 40–42.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_coordinate_approximation_norm {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i, |x i-y i| ≤ δ) : ‖x-y‖ ≤ δ*Real.sqrt n := by sorry

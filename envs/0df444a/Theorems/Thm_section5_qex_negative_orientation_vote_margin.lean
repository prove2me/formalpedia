-- Prove2me | Theorems.Thm_section5_qex_negative_orientation_vote_margin
-- name    : section5_qex_negative_orientation_vote_margin
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:35:34.386007+00:00
-- url     : https://prove2.me/theorems/8780035a-11ed-5ec6-9429-55fc71cdca21
-- title:
--   Finite-grid error margin for the opposite orientation
-- statement:
--   Let n≥1, q>0 and M=2^q≥1073741824n². Let w,u∈R^n be unit with ‖w+u‖≤1/6. For a grid example Z distributed according to normalized finite Gaussian weights, $$\Pr[\operatorname{ltf}_{w,0}(Z)=\operatorname{ltf}_{u,0}(Z)]\le7/32.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5OrientationMargin.lean, lines 51–56. Uses the Gaussian-disagreement foundation by kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_gaussian_disagreement_proved
import Theorems.Thm_section5_ideal_phase_distance_sq
import Theorems.Thm_section5_ideal_phase_neg
import Theorems.Thm_section5_normalized_phase_sum_eq_qex
import Theorems.Thm_section5_orientation_phase_error_small
import Theorems.Thm_section5_qex_phase_agreement
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_qex_negative_orientation_vote_margin (n q : ℕ) (hn : 1 ≤ n) (hq : 0 < q)
    (hgrid : 1073741824*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1) (hclose : ‖w+u‖ ≤ 1/6) :
    (∑ z : Qubits (n*q),
      if ltf w 0 (gridPoint z) = ltf u 0 (gridPoint z) then
        gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0) ≤ 7/32 := by sorry

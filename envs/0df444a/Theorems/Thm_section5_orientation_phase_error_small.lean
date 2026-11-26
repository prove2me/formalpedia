-- Prove2me | Theorems.Thm_section5_orientation_phase_error_small
-- name    : section5_orientation_phase_error_small
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:32:09.241981+00:00
-- url     : https://prove2.me/theorems/3df8503c-edd2-5f09-9377-88b2b0b402c0
-- title:
--   A large grid gives a small normalized phase-state error
-- statement:
--   Let n≥1, M>0 be natural numbers with M≥1073741824n², and let w∈R^n be unit. Let φ_w(x) be the standard Gaussian amplitude times the homogeneous-threshold phase, and let φ_(w,M) be its coordinatewise rounded, grid-box-restricted sampled counterpart. Then $$\left\|\frac{\phi_{w,M}}{\|\phi_{w,M}\|_{L^2}}-\phi_w\right\|_{L^2}\le1/6.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5OrientationVote.lean, lines 9–12. Uses the Gaussian-disagreement foundation by kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_hermite_discretization_budget
import Theorems.Thm_section5_normalized_phase_error
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_orientation_phase_error_small (n M : ℕ) (hn : 1 ≤ n) (hM : 0 < M)
    (hgrid : 1073741824*(n:ℝ)^2 ≤ M) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    ‖NormedSpace.normalize ((section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M))-
      (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)‖ ≤ 1/6 := by sorry

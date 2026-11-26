-- Prove2me | Theorems.Thm_section5_normalized_phase_distance_eq_qex
-- name    : section5_normalized_phase_distance_eq_qex
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:11:18.209259+00:00
-- url     : https://prove2.me/theorems/6f178374-5aac-43a0-beef-9c31f74e9f20
-- title:
--   Continuous sampled phase distance equals finite QEX distance
-- statement:
--   Let n,q be natural with q>0 and w,u∈R^n arbitrary. Let φ_(w,M),φ_(u,M) be the cell-constant sampled Gaussian phase functions on the M=2^q centered product grid, restricted to the grid box, and let Ψ_w,Ψ_u be their corresponding normalized finite Gaussian phase states in n q-bit registers. Then $$\left\|\frac{\phi_{w,M}}{\|\phi_{w,M}\|_{L^2}}-\frac{\phi_{u,M}}{\|\phi_{u,M}\|_{L^2}}\right\|_{L^2}=\|\Psi_w-\Psi_u\|_2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5PhaseDistanceTransfer.lean, lines 42–48.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_bit_phase_state_eq_qex_phase
import Theorems.Thm_section5_grid_lift_inner
import Theorems.Thm_section5_grid_lift_norm
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_normalized_phase_distance_eq_qex {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (hq : 0 < q) :
    ‖NormedSpace.normalize ((section5_sampled_phase_memLp w (2^q) (Nat.two_pow_pos q)).toLp
        (section5_sampled_phase_state w (2^q)))-
      NormedSpace.normalize ((section5_sampled_phase_memLp u (2^q) (Nat.two_pow_pos q)).toLp
        (section5_sampled_phase_state u (2^q)))‖ =
      ‖section5_qex_phase_input w q-section5_qex_phase_input u q‖ := by sorry

-- Prove2me | Theorems.Thm_section5_sampled_phase_toLp_ne_zero
-- name    : section5_sampled_phase_toLp_ne_zero
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:40.803927+00:00
-- url     : https://prove2.me/theorems/b45c2d30-70dc-4ec9-b4c1-fc66b8523b79
-- title:
--   A sampled threshold phase state is nonzero in L²
-- statement:
--   Let n,M be natural with M>0 and w∈R^n arbitrary. Let φ_(w,M)(x) be the rounded homogeneous-threshold sign at x times the sampled Gaussian amplitude, restricted to the source's centered M-grid box. Its Lebesgue L² class is nonzero: $$[\phi_{w,M}]_{L^2}\ne0.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5PhaseStateError.lean, lines 111–113.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_sampled_gaussian_toLp_ne_zero
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite

theorem section5_sampled_phase_toLp_ne_zero {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : ℕ) (hM : 0 < M) :
    (section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M) ≠ 0 := by sorry

-- Prove2me | Theorems.Thm_section5_power_column_magnitude_bounds
-- name    : section5_power_column_magnitude_bounds
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:29.418377+00:00
-- url     : https://prove2.me/theorems/9c7d89ee-5241-5925-a6af-11944726c33a
-- title:
--   Magnitude bounds for a maximum powered column
-- statement:
--   Let n≥1, L self-adjoint on C^n, w unit, 0≤η≤1/1000 and ‖L−ww*‖≤η. For natural k and j maximizing column norm of L^(k+1), $$2^{-(k+1)}\le2n\|L^{k+1}e_j\|,\qquad\|L^{k+1}e_j\|\le2^{k+1}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5PowerOutputPrecision.lean, lines 31–38.

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
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_column_norm_bound
import Theorems.Thm_section5_tomography_power_error
import Theorems.Thm_section5_tomography_rayleigh_lower
import Theorems.Thm_section5_top_eigenpair_exists
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_power_column_magnitude_bounds {n : ℕ} (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L)
    (w : EuclideanSpace ℂ (Fin n)) (hw : ‖w‖=1)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/1000) (herror : ‖L-rankOne ℂ w w‖ ≤ η)
    (k : ℕ) (j : Fin n) (hmax : ∀ i, ‖(L^(k+1)) (section5_coordinate_ket i)‖ ≤
      ‖(L^(k+1)) (section5_coordinate_ket j)‖) :
    (1/2:ℝ)^(k+1) ≤ 2*n*‖(L^(k+1)) (section5_coordinate_ket j)‖ ∧
      ‖(L^(k+1)) (section5_coordinate_ket j)‖ ≤ (2:ℝ)^(k+1) := by sorry

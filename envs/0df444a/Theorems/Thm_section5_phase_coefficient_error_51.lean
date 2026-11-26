-- Prove2me | Theorems.Thm_section5_phase_coefficient_error_51
-- name    : section5_phase_coefficient_error_51
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:32:02.559147+00:00
-- url     : https://prove2.me/theorems/87d097ab-53ea-5a0f-8768-dd1baf04d45a
-- title:
--   Low-degree phase coefficient error in Lemma 5.1
-- statement:
--   Let n,D,M be natural numbers with D≥1, M>0 and M≥64n²(D+1), and let w be a real unit vector in dimension n. Let S map the coefficient vector indexed by degree arrays α∈{0,…,D−1}^n to the tensor Hermite wavefunction. Let S_M use the same Hermite family evaluated at the coordinatewise rounded M-grid points and restricted to the grid box. Let φ_w be the Gaussian amplitude multiplied by the homogeneous-threshold phase, and φ_(w,M) its rounded, grid-restricted sampled counterpart, as defined in the source. Taking adjoints in the corresponding complex L² spaces,
--
--   $$‖S_M^*(φ_{w,M}/‖φ_{w,M}‖₂)−S^*φ_w‖₂≤24n√((D+1)/M)+2(8n/M)^{1/4}+2√(2n)e^{−πM/4}.$$
--
--   This is an analytic coefficient-discretization estimate.
-- source:
--   Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Section 5.1, Lemma 5.1, auxiliary synthesis-map formulation. Exact formalization: Solutions/Section5CoefficientDiscretization.lean, lines 97–103; synthesis and coefficient definitions, lines 77–93. Phase states: Solutions/Section5PhaseStateError.lean, lines 91–96.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CoefficientDiscretization
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5L2Synthesis
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_adjoint_supported_state_error
import Theorems.Thm_section5_complex_series_integral_sq
import Theorems.Thm_section5_hermite_roundCoord_error
import Theorems.Thm_section5_hybrid_linear_bound
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_normalized_phase_error
import Theorems.Thm_section5_sampled_phase_toLp_ne_zero
import Theorems.Thm_section5_tensor_synthesis_bound
import Theorems.Thm_section5_tensor_synthesis_error
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

theorem section5_phase_coefficient_error_51 (n D M : ℕ) (hD : 1 ≤ D) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    ‖section5_sampled_phase_coefficients w D M hM-
      ContinuousLinearMap.adjoint (section5_full_hermite_synthesis n D)
        ((section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w))‖ ≤
      24*n*Real.sqrt ((D+1)/M)+2*(8*n/M)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by sorry

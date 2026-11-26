-- Prove2me | Theorems.Thm_section5_bit_coefficient_error_51
-- name    : section5_bit_coefficient_error_51
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:42:44.14039+00:00
-- url     : https://prove2.me/theorems/5e9d6c7c-4d17-52cb-a545-d0c130c0360e
-- title:
--   Physical bit-register Hermite coefficient error
-- statement:
--   Let n,q,D be natural, q>0, D≥1, M=2^q≥64n²(D+1), and w∈R^n unit. Let Ψ_w be the normalized Gaussian grid state with homogeneous-threshold phase, encoded in n most-significant-bit-first q-bit registers. For degree arrays α∈{0,…,D−1}^n, let H_α be the tensor grid sampling of the normalized Hermite wavefunctions with the source's √(grid-cell-volume) normalization, and h_w(α) the continuous Gaussian Hermite coefficient. Then $$\left(\sum_\alpha|\langle H_\alpha,\Psi_w\rangle-h_w(\alpha)|^2\right)^{1/2}\le24n\sqrt{(D+1)/M}+2(8n/M)^{1/4}+2\sqrt{2n}e^{-\pi M/4}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5PhysicalHermiteGrid.lean, lines 102–108. Analytic context: Section 5.1, Lemma 5.1 and Appendix D; this auxiliary formulation does not assert the main quantum learning algorithm.

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
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5L2Synthesis
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_grid_lift_inner
import Theorems.Thm_section5_grid_lift_norm
import Theorems.Thm_section5_hermite_coefficient_error_51
import Theorems.Thm_section5_tensor_grid_vector_bits
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite

theorem section5_bit_coefficient_error_51 (n q D : ℕ) (hq : 0 < q) (hD : 1 ≤ D)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ (2:ℝ)^q) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖inner ℂ (section5_discrete_hermite_tensor n q D a) (section5_bit_phase_state w q)-
        (QuantumLTF.Membership.Supplement.hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤
      24*n*Real.sqrt ((D+1)/(2:ℝ)^q)+2*(8*n/(2:ℝ)^q)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4) := by sorry

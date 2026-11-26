-- Prove2me | Theorems.Thm_section5_continuous_coefficient_eq_hermCoeff
-- name    : section5_continuous_coefficient_eq_hermCoeff
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:29.70538+00:00
-- url     : https://prove2.me/theorems/03ca3838-cccb-52b9-8d32-260234fa2b42
-- title:
--   Continuous phase coefficients equal Gaussian Hermite coefficients
-- statement:
--   Let $n,D\in\mathbb N$, $w\in\mathbb R^n$, and $a\in\{0,\ldots,D-1\}^n$. Put $f_w(x)=\operatorname{sgn}\langle w,x\rangle$, with sign $+1$ at zero, $G(x)=\prod_i\sqrt{\varphi(x_i)}$, and $\psi_a(x)=\prod_i\sqrt{\varphi(x_i)}H_{a_i}(x_i)/\sqrt{a_i!}$, where $\varphi$ is the standard Gaussian density. If $T$ synthesizes the finite family $\psi_a$, then
--
--   $$[T^*(f_wG)]_a=\widehat f_w(a)=\mathbb E_{X\sim N(0,I_n)}\left[f_w(X)\prod_i\frac{H_{a_i}(X_i)}{\sqrt{a_i!}}\right].$$
--
--   The identity connects Lebesgue-space wavefunction coefficients to the Gaussian Hermite coefficients used for learning.
-- source:
--   Original coefficient-identification result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1, Hermite coefficient convention including Eq. (159). Formalization: Solutions/Section5HermiteCoefficientIdentification.lean, lines 41–85.

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
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5L2Synthesis
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_gaussian_pi_density
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Membership.Supplement
  QuantumLTF.Example Aux_w_53_hermite

theorem section5_continuous_coefficient_eq_hermCoeff {n D : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (a : Fin n → Fin D) :
    ContinuousLinearMap.adjoint (section5_full_hermite_synthesis n D)
        ((section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)) a =
      (hermCoeff w (fun i => (a i : ℕ)) : ℂ) := by sorry

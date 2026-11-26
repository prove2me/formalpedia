-- Prove2me | Theorems.Thm_section5_hermite_coefficient_error_51
-- name    : section5_hermite_coefficient_error_51
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:37:45.554161+00:00
-- url     : https://prove2.me/theorems/3baa0ca2-8f12-4719-b7bc-16004f56cacd
-- title:
--   Sampled phase-state Hermite coefficient error
-- statement:
--   Let $n,D,M\in\mathbb N$ with $D\ge1$, $M\ge1$, and $M\ge64n^2(D+1)$, and let $w\in\mathbb R^n$ be a unit vector. Let $\widehat f_w(a)$ be the Gaussian Hermite coefficients of $f_w(x)=\operatorname{sgn}\langle w,x\rangle$. Let $c_{w,D,M}$ be the adjoint synthesis coefficients of the normalized sampled phase state on the centered $M$-point grid, against the degree-$<D$ Hermite wavefunctions sampled on the same grid. Then
--
--   $$\left(\sum_{a\in\{0,\ldots,D-1\}^n}|c_{w,D,M}(a)-\widehat f_w(a)|^2\right)^{1/2}\le24n\sqrt{\frac{D+1}M}+2(8n/M)^{1/4}+2\sqrt{2n}\,e^{-\pi M/4}.$$
--
--   This supplies the finite-degree coefficient estimate underlying the printed discretization lemma.
-- source:
--   Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1, analytic coefficient form of Lemma 5.1. Formalization: Solutions/Section5HermiteCoefficientIdentification.lean, lines 87–95; sampled synthesis conventions are in the imported Section 5 synthesis modules.

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
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_continuous_coefficient_eq_hermCoeff
import Theorems.Thm_section5_phase_coefficient_error_51
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Membership.Supplement
  QuantumLTF.Example Aux_w_53_hermite

theorem section5_hermite_coefficient_error_51 (n D M : ℕ) (hD : 1 ≤ D) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖section5_sampled_phase_coefficients w D M hM a-(hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤
      24*n*Real.sqrt ((D+1)/M)+2*(8*n/M)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by sorry

-- Prove2me | Theorems.Thm_section5_qex_discretization_half_budget
-- name    : section5_qex_discretization_half_budget
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:49:04.400435+00:00
-- url     : https://prove2.me/theorems/45b8a72a-35eb-452e-b69d-60c7107060ce
-- title:
--   Explicit grid conditions for an error of at most $\eta/2$
-- statement:
--   Let $q,D\ge1$, $n\in\mathbb N$, $\eta>0$, and $w\in\mathbb R^n$ with $\|w\|=1$. Put $M=2^q$ and suppose $M\ge64n^2(D+1)$ as well as
--
--   $$M\ge\frac{20736n^2(D+1)}{\eta^2},\qquad M\ge\frac{165888n}{\eta^4},\qquad M\ge\frac4\pi\log\!\left(\frac{12\sqrt{2n}}\eta\right).$$
--
--   Let $\Psi_{w,q}$ be the normalized QEX phase input, $d_a$ the tensor discrete Hermite ket for $a\in\{0,\ldots,D-1\}^n$, and $\widehat f_w(a)$ the Gaussian Hermite coefficient of $\operatorname{sgn}\langle w,x\rangle$. Then
--
--   $$\left(\sum_a|\langle d_a,\Psi_{w,q}\rangle-\widehat f_w(a)|^2\right)^{1/2}\le\eta/2.$$
--
--   This supplies an explicit half-budget for the analytic discretization part of a subsequent conditional transform estimate.
-- source:
--   Original error-budget specialization of Lemma 5.1 in Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1. Formalization: Solutions/Section5DiscretizationLemma.lean, lines 48–59.

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
import Mathlib
import Theorems.Thm_section5_hermite_discretization_budget
import Theorems.Thm_section5_lemma_5_1
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_qex_discretization_half_budget (n q D : ℕ) (hq : 0 < q) (hD : 1 ≤ D)
    (η : ℝ) (hη : 0 < η) (hsize : 64*(n:ℝ)^2*(D+1) ≤ (2:ℝ)^q)
    (h1 : 20736*(n:ℝ)^2*(D+1)/η^2 ≤ (2:ℝ)^q)
    (h2 : 165888*(n:ℝ)/η^4 ≤ (2:ℝ)^q)
    (h3 : 4/Real.pi*Real.log (12*Real.sqrt (2*n)/η) ≤ (2:ℝ)^q)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖inner ℂ (section5_flat_hermite_tensor n q D a) (section5_qex_phase_input w q)-
        (hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤ η/2 := by sorry

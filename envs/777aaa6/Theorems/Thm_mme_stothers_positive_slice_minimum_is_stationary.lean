-- Prove2me | Theorems.Thm_mme_stothers_positive_slice_minimum_is_stationary
-- name    : mme_stothers_positive_slice_minimum_is_stationary
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-21T23:14:30.218116+00:00
-- url     : https://prove2.me/theorems/84908432-1114-490c-be70-a3c8d26b1315
-- title:
--   Positive entropy minima on a marginal slice are stationary
-- statement:
--   Let $Z$ be the normalized nonnegative fourth-power profile space, with class multiplicities $n_i$, and let $Y$ be its two-dimensional marginal kernel. Write $\mathcal E(c)=\prod_i c_i^{n_i c_i}$. Suppose $b\in Z$ has strictly positive coordinates and minimizes $\mathcal E$ among all $c\in Z$ with $c-b\in Y$. Then, using indices $0,\ldots,9$,
--
--   $$b_2 b_7^2=b_4 b_5 b_9,\qquad b_3 b_7 b_8=b_4 b_6 b_9.$$
--
--   Thus $b$ belongs to the stationary set $\mathcal N$. This supplies the necessity direction of the positive slice-minimum characterization and allows value bounds stated for stationary profiles to be applied to attained positive entropy minima.
--
--   **Formalization Note** The equations use the corrected class ordering and stationarity equations in the platform's fourth-power data interface.
-- source:
--   Derived stationarity-necessity lemma from the entropy calculus in A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Roy. Soc. Edinburgh A 143 (2013), printed p. 368, proof of Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This is the converse calculus step, not a separately numbered theorem in the paper; equations follow the corrected platform fourth-power data interface.

import Definitions.Def_mme_stothers_fourth_data
open MME.StothersFourth
set_option autoImplicit false

theorem mme_stothers_positive_slice_minimum_is_stationary
    (b : Fin 10 → ℝ) (hb : InZ b) (hbpos : ∀ i, 0 < b i)
    (hmin : ∀ c : Fin 10 → ℝ, InZ c →
      InY (fun i ↦ c i - b i) → entropyProduct b ≤ entropyProduct c) :
    InN b := by sorry

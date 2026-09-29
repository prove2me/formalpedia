-- Prove2me | Theorems.Thm_mme_dwz_global_behrend_retained_count_normalization
-- name    : mme_dwz_global_behrend_retained_count_normalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:15:44.528605+00:00
-- url     : https://prove2.me/theorems/4ecc6f2b-bb5a-4f18-b2f1-ec0d0c884848
-- title:
--   Global Behrend bucket retention with the exact DWZ hash denominator
-- statement:
--   Let $p,A,n$ be positive-count parameters, let $S$ be a finite progression-free set, and let $E,D$ be real normalization factors with $D>0$. Suppose the common-prime estimate gives $pE\le 16D A$, the Behrend set satisfies
--
--   $$\lfloor p/2\rfloor\,e^{-4\sqrt{\log \lfloor p/2\rfloor}}\le |S|,$$
--
--   and a global affine bucket retains at least $A|S|/(2p^2)$ objects. Then the retained count obeys
--
--   $$E\,\frac{(\lfloor p/2\rfloor/p)e^{-4\sqrt{\log \lfloor p/2\rfloor}}}{32D}\le n.$$
--
--   This is the exact finite arithmetic step used to pass from a global exact-profile first-hash retention bound to the displayed loss in DWZ Equation (21), without introducing a separate coarse-$Z$ replication factor.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21) and Sections 3.10 and 6.2; https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option autoImplicit false

theorem mme_dwz_global_behrend_retained_count_normalization
    (p A n : ℕ) (S : Finset ℕ) (E D : ℝ)
    (hppos : 0 < p) (hD : 0 < D)
    (hprime : (p : ℝ) * E ≤ 16 * D * (A : ℝ))
    (hbehrend :
      ((p / 2 : ℕ) : ℝ) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
        (S.card : ℝ))
    (hretained :
      ((A : ℝ) * (S.card : ℝ)) / (2 * (p : ℝ) ^ 2) ≤ (n : ℝ)) :
    E *
        (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))))) /
        (32 * D) ≤
      (n : ℝ) := by
  sorry

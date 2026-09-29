-- Prove2me | Theorems.Thm_mme_dwz_table2_exact_hash_lower_eventually_two_groups
-- name    : mme_dwz_table2_exact_hash_lower_eventually_two_groups
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T19:59:08.375439+00:00
-- url     : https://prove2.me/theorems/22c083d2-af00-4d75-a768-78025432ea0e
-- title:
--   The exact Table-2 retained count eventually contains two Hole-repair groups
-- statement:
--   Let $L$ be the Table-2 word length and let $p$ be any admissible common prime with $2\le p\le\exp(16(L+1))$. Write
--
--   $$
--   D_{\rm hash}=32\max\bigl((6x)^{15}(6x)^5x^{15},(6x)^5(6x)^9\bigr),\qquad x=L+1.
--   $$
--
--   The exact finite lower bound retained by asymmetric hashing is
--
--   $$
--   A_L(p)=2^{\rho L}\,\frac{\lfloor p/2\rfloor}{p}\,\frac{\exp\!\left(-4\sqrt{\log\lfloor p/2\rfloor}\right)}{D_{\rm hash}},
--   $$
--
--   where $\rho$ is the exact Table-2 retained logarithmic rate. For every sufficiently large $L$, uniformly for every such $p$,
--
--   $$
--   2\cdot 8(4L+1)\le A_L(p).
--   $$
--
--   Thus the exact retained family contains at least two complete groups of the size required by Corollary 5.11; the prime, polynomial, and Behrend losses are all retained explicitly.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Corollary 5.11 and the finite retained-count estimate leading to Equations (24)--(25), printed pp. 48 and 58--59; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_retained_log_rate_gt_157133
import Theorems.Thm_mme_floor_behrend_polynomial_loss_ge_exp_sqrt
import Theorems.Thm_mme_dwz_table2_retained_polynomial_denominator_le_exp_sqrt
import Theorems.Thm_mme_eventually_linear_le_exp_linear_sub_sqrt

open Filter Topology
open MME.DWZSquare

set_option autoImplicit false

theorem mme_dwz_table2_exact_hash_lower_eventually_two_groups :
    ∀ᶠ L : ℕ in atTop,
      ∀ p : ℕ, 2 ≤ p →
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) →
        let x : ℝ := (((L + 1 : ℕ) : ℝ))
        let jointPoly : ℝ := (6 * x) ^ 15
        let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
        let zPoly : ℝ := (6 * x) ^ 5
        let compatibilityPoly : ℝ := (6 * x) ^ 9
        let Dhash : ℝ :=
          32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
        2 * ((8 * (4 * L + 1) : ℕ) : ℝ) ≤
          Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              Dhash) := by
  sorry

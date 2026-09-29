-- Prove2me | Theorems.Thm_mme_released_116_arbitrarily_large_size_test
-- name    : mme_released_116_arbitrarily_large_size_test
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:33:11.727612+00:00
-- url     : https://prove2.me/theorems/18b57983-17dc-42cc-9b21-dcd679ade8a2
-- title:
--   Arbitrarily large released scales satisfy the extraction size test
-- statement:
--   For every tolerance $\varepsilon>0$ and every integer lower bound $K$, there is an integer $k\ge K$ with $k>0$ such that
--   $$16\bigl(25\cdot6\cdot|W_2|^2\bigr)\le kd^2\varepsilon^2,$$
--   where $W_2$ is the set of complete level-two child words and $d=10^{12}$. This is the integer extraction size test with repair scale two and minimum $kd^2$.
-- source:
--   Integer replication of regional profiles and the released owner-zero (1,1,6) component.

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NormNum

open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
set_option autoImplicit false

theorem mme_released_116_arbitrarily_large_size_test
    (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧
      (8 * 2 : ℝ) * (25 * 6 *
        (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2) ≤
        (k * denominator ^ 2 : ℕ) * eps ^ 2 := by sorry

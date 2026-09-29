-- Prove2me | Theorems.Thm_mme_CW_coupled_pruning_ratio
-- name    : mme_CW_coupled_pruning_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:30:22.026769+00:00
-- url     : https://prove2.me/theorems/346a7339-9a5a-480c-8976-becd4cfa1ca3
-- title:
--   The coupled CW pruning ratio exceeds 3.41
-- statement:
--   In the optimized coupled-constituent extraction, the block proportions on journal p. 272 satisfy
--
--   $$
--   \frac{G}{L}=\frac{q^{3\tau}}{2}.
--   $$
--
--   If $q\ge 3$ and $3\tau\ge 2$, then this ratio is greater than $3.41$, the numerical threshold required by the collision-pruning estimate. In fact, it is at least $9/2$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled-piece proof on journal pp. 271--272 (PDF pp. 21--22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME Real

theorem mme_CW_coupled_pruning_ratio
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    (341 : ℝ) / 100 < (q : ℝ) ^ (3 * tau) / 2 := by sorry

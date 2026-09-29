-- Prove2me | Theorems.Thm_mme_degenerate_pow_rank_bound
-- name    : mme_degenerate_pow_rank_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-28T20:40:40.765255+00:00
-- url     : https://prove2.me/theorems/1229269f-b0e4-403e-a6f1-4564ca4b5cfb
-- statement:
--   **Border rank gives subexponential rank growth.** If `X` degenerates from $I_r$ (border rank $\le r$), the rank of its Kronecker powers obeys $\mathrm{rank}(X^{\otimes(n+1)})\le r^{n+1}\cdot C(n+1)$ for a subexponential factor $C$ with $C\ge1$ and $C(n+1)^{1/(n+1)}\to1$ (concretely $C(m)=(mh+1)^d$ from the order-$h$ degeneration truncation).
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
open MME Filter Topology
universe u

theorem mme_degenerate_pow_rank_bound {K : Type u} [Field K] {d : ℕ}
    {X : TensorObj K d} {r : ℕ} (h : Degenerates X (TensorObj.diagObj K d r)) :
    ∃ C : ℕ → ℝ, (∀ n, (1 : ℝ) ≤ C n) ∧
      Filter.Tendsto (fun n => (C (n + 1)) ^ ((1 : ℝ) / (n + 1))) Filter.atTop (nhds 1) ∧
      ∀ n, (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ) ≤ (r : ℝ) ^ (n + 1) * C (n + 1) := by sorry

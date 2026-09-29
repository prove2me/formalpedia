-- Prove2me | Theorems.Thm_mme_hash_extraction_cofinal_rate_of_log_bounds
-- name    : mme_hash_extraction_cofinal_rate_of_log_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:46:10.264608+00:00
-- url     : https://prove2.me/theorems/6fad4b4a-9920-44a7-a818-134139d4c37a
-- title:
--   Cofinal hash rates with an explicit vanishing rounding loss
-- statement:
--   Let $D_n$ be finite hash-extraction data with ambient powers $P_n\to\infty$. Fix real $\tau,c,w$ with $c>0$ and $c+w>6\log2401$. Suppose that eventually all factor lower bounds $L_{n,j}$ and matrix volumes $M_n$ are positive and
--   $$cP_n\le\sum_j\log L_{n,j}-\log r_n,\qquad wP_n\le\tau\log M_n,$$
--   where $r_n$ is the repair-copy count. Then there is $V>2401$ such that, eventually,
--   $$(V^6)^{P_n}(1-e^{-cP_n})\le\operatorname{rate}_{D_n}(\tau),$$
--   and the error $e^{-cP_n}$ tends to zero. This supplies the scalar rate and vanishing-error requirements of the cofinal certificate. Tensor realization and finite stage budgets remain independent requirements.
-- source:
--   Exact certified copy-count formula and exponential/logarithmic inequalities.

import Definitions.Def_mme_hash_extraction_certificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MME MME.HashExtraction Filter
open scoped BigOperators Topology
set_option autoImplicit false

theorem mme_hash_extraction_cofinal_rate_of_log_bounds
    (D : ℕ → Data) (tau c w : ℝ) (hc : 0 < c)
    (hgap : 6 * Real.log 2401 < c + w)
    (hpower : Tendsto (fun n ↦ (D n).power) atTop atTop)
    (hdata : ∀ᶠ n in atTop,
      (∀ j, 0 < ((D n).hash j).lower) ∧
      0 < (D n).a * (D n).b * (D n).c ∧
      c * (D n).power ≤
        (∑ j, Real.log ((D n).hash j).lower) - Real.log (D n).repairCopies ∧
      w * (D n).power ≤ tau * Real.log (((D n).a * (D n).b * (D n).c : ℕ) : ℝ)) :
    ∃ V : ℝ, 2401 < V ∧
      Tendsto (fun n ↦ Real.exp (-(c * (D n).power))) atTop (nhds 0) ∧
      ∀ᶠ n in atTop,
        (V ^ (6 : ℕ)) ^ (D n).power * (1 - Real.exp (-(c * (D n).power))) ≤
          (D n).rate tau := by sorry

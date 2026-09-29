-- Prove2me | Theorems.Thm_BonferroniMarginals_chung_erdos_dominates_bonferroni
-- name    : BonferroniMarginals.chung_erdos_dominates_bonferroni
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:09:32.849192+00:00
-- url     : https://prove2.me/theorems/138c022b-2224-48b6-9a45-e201389556f0
-- title:
--   **The second-moment bound dominates the Bonferroni bound throughout the
-- statement:
--   **The second-moment bound dominates the Bonferroni bound throughout the
--   Bonferroni regime.**  Whenever `2(k-1) ≤ M` — the hypothesis of
--   `AlmostLossless.failure_prob_lower_bound_real` — the new bound `k/(M+k-1)` is at
--   least the old bound `k/(2M)`.  So nothing is lost and the regime restriction is
--   removed.
--
--   ```lean
--   theorem BonferroniMarginals.chung_erdos_dominates_bonferroni{k M : ℕ} (hM : 0 < M) (hk : k ≤ M + 1) :
--       (k : ℝ) / (2 * M) ≤ (k : ℝ) / ((M : ℝ) + k - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/BonferroniMarginals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/BonferroniMarginals.lean#L311

-- Thm stub generated from Geometry/BonferroniMarginals.lean
import Mathlib
import Definitions.Def_Geometry_BonferroniMarginals
/-
# Which marginals? — the second-moment upgrade of the Bonferroni machinery

Research thread *Compression Beyond the Pigeonhole Bound*, cycle v19c.

`Geometry.AlmostLosslessConverse` formalises the **second Bonferroni inequality**
(`AlmostLossless.card_sum_le_card_biUnion_add_offDiag`) for an *arbitrary* finite
family of finite sets and feeds it two marginals of the uniform random codebook:

* the first marginal `M · |{H : H p = H q}| = M^{|ι|}` (probability `1/M`), and
* the second marginal `M² · |{H : H p = H r = H q}| ≤ M^{|ι|}` (probability `1/M²`).

The output is the failure bound `P[failure] ≥ k/(2M)`, valid **only** in the
regime `2(k-1) ≤ M`.  This file asks the structural question suggested by that
shape: *is the regime restriction a property of the marginals, or of the
machinery?*  The answer proved here is: **of the machinery**.

Contents.

* `BonferroniMarginals.sq_sum_card_le_card_biUnion_mul_sum_inter` — the
  **Chung–Erdős / second-moment (Paley–Zygmund) inequality in exact counting
  form**, for an arbitrary finite family of finite sets:
  `(∑ |A i|)² ≤ |⋃ A i| · ∑_{(i,j)} |A i ∩ A j|`.
  Proved from scratch by double counting the multiplicity function
  `f w = #{i ∈ I : w ∈ A i}` and Cauchy–Schwarz.
* `BonferroniMarginals.card_biUnion_lower_of_marginals` — the abstract
  *marginal-profile* theorem.  A family with **first marginal `1/m`** and
  **second marginal `≤ 1/c`** satisfies
  `c·k·N ≤ m·|⋃ A i|·(c + m(k-1))`, i.e. `P[⋃] ≥ k / (m + m²(k-1)/c)`,
  with **no upper restriction on `k`**.
* `BonferroniMarginals.marginal_bound_sharp` — the abstract theorem is
  **attained**: a constant family with `c = m` turns the inequality into an
  equality, so no improvement is possible from the marginal profile alone.
* `BonferroniMarginals.bonferroni_conclusion_fails_without_pairwise` — the
  Bonferroni conclusion `|⋃| ≥ kN/(2m)` is *false* for that same family:
  the second marginal is genuinely load-bearing.
* `BonferroniMarginals.hashing_failure_lower_unconditional` — feeding the two
  catalog marginals into the second-moment machinery instead of into Bonferroni
  yields `k · M^{|α|} ≤ |failSet| · (M + k - 1)`, i.e.
  `P[failure] ≥ k/(M+k-1)` **unconditionally**.
* `BonferroniMarginals.chung_erdos_dominates_bonferroni` — in the whole
  Bonferroni regime `2(k-1) ≤ M` the new bound is at least as strong.
* `BonferroniMarginals.hashing_failure_above_rate` — the new bound has content
  the Bonferroni bound cannot have: for `k ≥ M` a uniformly random codebook
  fails with probability `> 1/2`.  Random hashing therefore has a genuine
  *converse*, matching the pigeonhole converse `converse_card_good_le`.
-/

open BonferroniMarginals

-- open removed: section is not a namespace

/-! ## 1. The second-moment (Chung–Erdős) inequality in counting form -/


/-! ## 2. The abstract marginal-profile theorem -/



/-! ## 3. Sharpness of the abstract theorem, and necessity of the second marginal

The extremal family is the constant one: `k` copies of a single atom in a space
of size `N = m`.  Its first marginal is exactly `1/m`, its second marginal is
also `1/m` (the worst possible, `c = m`), and its union has probability exactly
`1/m` however large `k` is. -/




/-! ## 4. Feeding the catalog's two marginals into the second-moment machinery -/

-- open removed: section is not a namespace

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}

theorem BonferroniMarginals.chung_erdos_dominates_bonferroni{k M : ℕ} (hM : 0 < M) (hk : k ≤ M + 1) :
    (k : ℝ) / (2 * M) ≤ (k : ℝ) / ((M : ℝ) + k - 1) := by sorry

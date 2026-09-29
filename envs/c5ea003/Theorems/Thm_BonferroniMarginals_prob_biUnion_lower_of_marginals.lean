-- Prove2me | Theorems.Thm_BonferroniMarginals_prob_biUnion_lower_of_marginals
-- name    : BonferroniMarginals.prob_biUnion_lower_of_marginals
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:09:40.258985+00:00
-- url     : https://prove2.me/theorems/df4d3aeb-6cd2-42a9-9685-60a7e1c5373d
-- title:
--   Real-valued form of the marginal-profile theorem: the union has probability
-- statement:
--   Real-valued form of the marginal-profile theorem: the union has probability
--   at least `c·k / (m·(c + m(k-1)))`.
--
--   ```lean
--   theorem BonferroniMarginals.prob_biUnion_lower_of_marginals{ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
--       (A : ι → Finset Ω) (I : Finset ι) {m c N : ℕ} (hN : 0 < N) (hm : 0 < m)
--       (hc : 0 < c) (hmarg : ∀ i ∈ I, m * (A i).card = N)
--       (hpair : ∀ p ∈ I.offDiag, c * (A p.1 ∩ A p.2).card ≤ N) :
--       (c : ℝ) * I.card / ((m : ℝ) * (c + m * ((I.card : ℝ) - 1)))
--         ≤ ((I.biUnion A).card : ℝ) / N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/BonferroniMarginals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/BonferroniMarginals.lean#L164

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

theorem BonferroniMarginals.prob_biUnion_lower_of_marginals{ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (A : ι → Finset Ω) (I : Finset ι) {m c N : ℕ} (hN : 0 < N) (hm : 0 < m)
    (hc : 0 < c) (hmarg : ∀ i ∈ I, m * (A i).card = N)
    (hpair : ∀ p ∈ I.offDiag, c * (A p.1 ∩ A p.2).card ≤ N) :
    (c : ℝ) * I.card / ((m : ℝ) * (c + m * ((I.card : ℝ) - 1)))
      ≤ ((I.biUnion A).card : ℝ) / N := by sorry

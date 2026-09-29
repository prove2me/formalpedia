-- Prove2me | Definitions.Def_Geometry_BonferroniMarginals
-- name    : Geometry_BonferroniMarginals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:33:24.099111+00:00
-- url     : https://prove2.me/theorems/11264c81-c329-4af0-925c-0d0cd245b4a6
-- title:
--   Aether Catalog definitions — Geometry_BonferroniMarginals
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.BonferroniMarginals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/BonferroniMarginals.lean by skeleton subtraction
import Mathlib
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

namespace BonferroniMarginals

open Finset

/-! ## 1. The second-moment (Chung–Erdős) inequality in counting form -/


/-! ## 2. The abstract marginal-profile theorem -/



/-! ## 3. Sharpness of the abstract theorem, and necessity of the second marginal

The extremal family is the constant one: `k` copies of a single atom in a space
of size `N = m`.  Its first marginal is exactly `1/m`, its second marginal is
also `1/m` (the worst possible, `c = m`), and its union has probability exactly
`1/m` however large `k` is. -/

/-- The constant family `A i = {0}` in `Fin 2`, indexed by three points. -/
private def cst : ℕ → Finset (Fin 2) := fun _ => {0}



/-! ## 4. Feeding the catalog's two marginals into the second-moment machinery -/



variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}





end BonferroniMarginals



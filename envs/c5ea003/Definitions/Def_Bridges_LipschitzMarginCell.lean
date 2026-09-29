-- Prove2me | Definitions.Def_Bridges_LipschitzMarginCell
-- name    : Bridges_LipschitzMarginCell
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:48.898474+00:00
-- url     : https://prove2.me/theorems/1250b222-5dfc-40b4-b481-c150fef0fd7a
-- title:
--   Aether Catalog definitions — Bridges_LipschitzMarginCell
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LipschitzMarginCell`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LipschitzMarginCell.lean by skeleton subtraction
import Mathlib

/-!
# Lipschitz Ball Inclusion in Margin Cells and Intrinsic Radius Bounds

This file proves that certified robustness balls, determined by a local margin and
a Lipschitz constant, are contained in the entire margin cell of the predicted class,
even when the competing label set is infinite. We then derive Chebyshev-radius lower
bounds for decision cells.

## Main definitions

* `marginCell` — the set of points where class `i` strictly dominates all competitors
* `inscribedRadiusAt` — the supremum of radii of closed balls centered at `x` in a set

## Main results

* `lipschitz_lower_bound` — a Lipschitz function's value at `y` is bounded below by its
  value at `x` minus `K * dist x y`
* `ball_subset_marginCell_of_pairwise_lipschitz` — the open ball of radius `γ / K`
  around `x` is contained in the margin cell
* `exists_pos_ball_subset_marginCell` — existential version
* `closedBall_subset_marginCell_of_lt` — closed balls of radius `< γ/K` are in the cell
* `certifiedRadius_le_inscribedRadiusAt_marginCell` — the certified radius `γ / K` is
  a lower bound on the inscribed radius when the set is bounded above

## Key insight

The proof does not require finiteness of the label set `ι`. If the hypotheses provide
a uniform margin `γ` and pairwise Lipschitz bound `K` for every competitor, the geometry
is infinitary for free.
-/

open Metric Set

noncomputable section

/-! ### Definitions -/

/-- The margin cell of class `i`: the set of points where the score of `i` strictly
    exceeds the score of every other class. This is a generalized weighted Voronoi region. -/
def marginCell {X ι : Type*} (s : ι → X → ℝ) (i : ι) : Set X :=
  {y | ∀ j, j ≠ i → s i y > s j y}

/-- The inscribed radius of a set `A` at a point `x`: the supremum of radii `r ≥ 0`
    such that `closedBall x r ⊆ A`. -/
def inscribedRadiusAt {X : Type*} [PseudoMetricSpace X] (A : Set X) (x : X) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ Metric.closedBall x r ⊆ A}

/-! ### Core lemma: Lipschitz lower bound -/


/-! ### Membership lemma -/


/-! ### Theorem A: Ball inclusion in margin cell -/


/-! ### Existential form -/


/-! ### Closed ball inclusions -/



/-! ### Theorem B: Inscribed radius lower bound -/

/-
**Inscribed radius lower bound.** When the set of valid inscribed radii is bounded
    above (which holds whenever the margin cell is a proper subset of the space), the
    certified radius `γ / K` is a lower bound on the inscribed radius at `x`.
-/

end



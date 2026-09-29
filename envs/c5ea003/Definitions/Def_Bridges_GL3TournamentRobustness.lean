-- Prove2me | Definitions.Def_Bridges_GL3TournamentRobustness
-- name    : Bridges_GL3TournamentRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:45.10325+00:00
-- url     : https://prove2.me/theorems/fed218b3-db73-44b8-86d7-e0433000996e
-- title:
--   Aether Catalog definitions — Bridges_GL3TournamentRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GL3TournamentRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GL3TournamentRobustness.lean by skeleton subtraction
import Mathlib
/-
# GL3 Tropical Satake Tournament Robustness

This file establishes robustness theorems for a pairwise-comparison (tournament)
classifier built from GL3 tropical Satake / Hecke score maps. The key results show
that if all pairwise score margins exceed twice the perturbation budget, then:
- the sign of every pairwise gap is preserved,
- the Condorcet (tournament) winner is invariant, and
- the Copeland score of the winner remains exactly 2.

The mathematical content is:
  tropical Lipschitz control on scores
  ⇒ Lipschitz control on pairwise gaps
  ⇒ sign stability of all decisive comparisons
  ⇒ invariance of tournament-based multiclass decisions.
-/


open Finset

variable {α : Type*}

/-! ## Core Definitions -/

/-- The pairwise gap between scores for classes `i` and `j`. -/
def gap (S : α → Fin 3 → ℝ) (x : α) (i j : Fin 3) : ℝ :=
  S x i - S x j

/-- Number of pairwise wins for class `i`: the count of classes `j ≠ i`
    such that `S x i > S x j`. -/
noncomputable def pairwiseWins (S : α → Fin 3 → ℝ) (x : α) (i : Fin 3) : ℕ :=
  (Finset.univ.filter fun j => j ≠ i ∧ 0 < gap S x i j).card

/-- Class `i` is a Condorcet winner if it beats every other class in
    pairwise comparison. -/
def isCondorcetWinner (S : α → Fin 3 → ℝ) (x : α) (i : Fin 3) : Prop :=
  ∀ j, j ≠ i → 0 < gap S x i j

/-- A strict tournament has no ties: every pair of distinct classes has
    a nonzero gap. -/
def strictTournament (S : α → Fin 3 → ℝ) (x : α) : Prop :=
  ∀ i j, i ≠ j → gap S x i j ≠ 0

/-! ## Sign Preservation Under Perturbation -/

/-
**Sign preservation lemma.** If a real number `a` is perturbed to `b`
    with `|b - a| ≤ ε` and `ε < |a|`, then `a` and `b` have the same sign.
-/

/-! ## Gap Perturbation Bound -/

/-
The perturbation of a pairwise gap is bounded by twice the coordinatewise
    score perturbation: if each score changes by at most `K * d * r`, then
    each gap changes by at most `2 * K * d * r`.
-/

/-! ## Gap Sign Stability -/

/-
**Gap sign stability.** If all pairwise gaps are perturbed by at most
    `2 * K * d * r`, and every gap's absolute value exceeds this bound,
    then all gap signs are preserved.
-/

/-! ## Condorcet Winner Stability -/

/-
**Condorcet winner stability.** If class `c` beats every rival by more than
    the perturbation budget `2 * K * d * r`, then `c` remains a Condorcet
    winner after perturbation. This is the main robustness theorem.
-/

/-! ## Copeland Score of a Condorcet Winner -/

/-
A Condorcet winner on `Fin 3` has Copeland score (pairwise wins) exactly 2.
-/

/-
**Copeland score stability.** Combining Condorcet stability with the
    Copeland score computation: class `c` has Copeland score 2 after perturbation.
-/

/-! ## Full GL3 Robustness Theorem -/

/-
**GL3 Tournament Robustness Theorem.** Starting from coordinatewise score
    perturbation bounds `|S x' i - S x i| ≤ K * d * r`, if every gap from the
    winning class `c` exceeds `2 * K * d * r`, then `c` remains a Condorcet
    winner. This derives the gap perturbation bound internally.
-/

/-! ## Strict Tournament Orientation Stability -/

/-
**All-edges orientation stability.** If all pairwise margins exceed the
    perturbation budget, then the orientation of every edge in the tournament
    is preserved. This implies invariance of any decision rule that depends
    only on edge orientations.
-/

/-! ## Condorcet Winner Existence and Cycles -/

/-
A Condorcet winner exists on `Fin 3` if and only if the tournament has
    no 3-cycle.
-/



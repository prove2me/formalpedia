-- Prove2me | Definitions.Def_Bridges_IRVStability
-- name    : Bridges_IRVStability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:33.117317+00:00
-- url     : https://prove2.me/theorems/82f34663-5718-4a0f-aefd-3b59dced7d48
-- title:
--   Aether Catalog definitions — Bridges_IRVStability
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IRVStability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IRVStability.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GL3 Tropical Satake Certified Robustness for IRV Classifiers

This file formalizes a robustness theory for deterministic, tie-free
instant-runoff / sequential-elimination classifiers built from multiclass
tropical score maps.

## Main results

* `roundLoser_eq_of_strict_min` — uniqueness of the minimizer on a finite set
* `gap_preserved_under_perturbation` — the one-round perturbation lemma
* `eliminationOrderOn_stable` — elimination-order stability under bounded perturbation
* `irvWinnerOn_stable` — winner stability under bounded perturbation
* `irvWinner_certified_robust` — the full tropical/Lipschitz robustness corollary

## Proof architecture

The core theorem proceeds by induction on the cardinality of the active
candidate set. At each round, the gap certificate ensures the current loser
has score at least γ below every other active candidate. A uniform
perturbation of size ≤ ε shifts each score by at most ε, so the gap shrinks
by at most 2ε. When 2ε < γ, the same candidate remains the unique loser,
and the induction carries through the remaining rounds.
-/


namespace IRV

open Finset

/-! ## Part 1: Core Definitions -/


/-- Gap certificate: `i` is in `S` and every other element of `S` has
    score at least `γ` above `v i`. -/
def HasGapAtLeast {m : ℕ} (S : Finset (Fin m)) (v : Fin m → ℝ)
    (i : Fin m) (γ : ℝ) : Prop :=
  i ∈ S ∧ ∀ j ∈ S, j ≠ i → v i + γ ≤ v j

/-- The round loser: the element of `S` minimizing `v`, chosen via `Classical.choose`
    from the existence of a minimizer on a nonempty finite set. -/
noncomputable def roundLoser {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (v : Fin m → ℝ) : Fin m :=
  (S.exists_min_image v hS).choose

/-! ## Part 2: Properties of `roundLoser` -/

lemma roundLoser_mem {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (v : Fin m → ℝ) : roundLoser S hS v ∈ S :=
  (S.exists_min_image v hS).choose_spec.1


/-
If `i ∈ S` is strictly below every other element of `S` under `v`,
    then `roundLoser S hS v = i`.
-/

/-! ## Part 3: Recursive Elimination -/

private lemma erase_nonempty_of_card_gt_one {m : ℕ} {S : Finset (Fin m)}
    {a : Fin m} (ha : a ∈ S) (hcard : ¬ S.card ≤ 1) :
    (S.erase a).Nonempty := by
  -- Since S has more than one element, removing one element a from S leaves a set with at least one element.
  have h_card_erase : (S.erase a).card ≥ 1 := by
    grind +locals;
  -- Since the cardinality of S.erase a is at least 1, the set must be nonempty.
  apply Finset.card_pos.mp h_card_erase

private lemma erase_card_lt {m : ℕ} {S : Finset (Fin m)}
    {a : Fin m} (ha : a ∈ S) :
    (S.erase a).card < S.card := by
  grind +locals

/-- Recursive elimination order on active set `S`: produces the list
    `[first_eliminated, second_eliminated, ..., winner]`. -/
noncomputable def eliminationOrderOn {m : ℕ}
    (S : Finset (Fin m)) (hS : S.Nonempty) (v : Fin m → ℝ) : List (Fin m) :=
  if hcard : S.card ≤ 1 then
    [S.min' hS]
  else
    let i := roundLoser S hS v
    have hi : i ∈ S := roundLoser_mem S hS v
    have hS' : (S.erase i).Nonempty := erase_nonempty_of_card_gt_one hi hcard
    have : (S.erase i).card < S.card := erase_card_lt hi
    i :: eliminationOrderOn (S.erase i) hS' v
termination_by S.card

/-- The IRV winner on active set `S`: the last candidate surviving
    sequential elimination by minimum score. -/
noncomputable def irvWinnerOn {m : ℕ}
    (S : Finset (Fin m)) (hS : S.Nonempty) (v : Fin m → ℝ) : Fin m :=
  if hcard : S.card ≤ 1 then
    S.min' hS
  else
    let i := roundLoser S hS v
    have hi : i ∈ S := roundLoser_mem S hS v
    have hS' : (S.erase i).Nonempty := erase_nonempty_of_card_gt_one hi hcard
    have : (S.erase i).card < S.card := erase_card_lt hi
    irvWinnerOn (S.erase i) hS' v
termination_by S.card

/-- The IRV winner on all candidates. -/
noncomputable def irvWinner {m : ℕ} [NeZero m] (v : Fin m → ℝ) : Fin m :=
  irvWinnerOn Finset.univ Finset.univ_nonempty v

/-- Recursive gap certificate: at every round of the elimination of `v` on `S`,
    the current loser has gap at least `γ` to every other active candidate. -/
noncomputable def EliminationGapCertified {m : ℕ}
    (S : Finset (Fin m)) (hS : S.Nonempty) (v : Fin m → ℝ) (γ : ℝ) : Prop :=
  if hcard : S.card ≤ 1 then
    True
  else
    let i := roundLoser S hS v
    have hi : i ∈ S := roundLoser_mem S hS v
    have hS' : (S.erase i).Nonempty := erase_nonempty_of_card_gt_one hi hcard
    have : (S.erase i).card < S.card := erase_card_lt hi
    HasGapAtLeast S v i γ ∧ EliminationGapCertified (S.erase i) hS' v γ
termination_by S.card

/-! ## Part 4: One-Round Perturbation Lemma -/

/-
The algebraic heart: if `i` has gap `γ` in `S` under `v`, and `v'` is
    within `ε` of `v` coordinatewise, then `i` still has gap `γ - 2*ε`
    in `S` under `v'`.
-/

/-
From a preserved positive gap, the same candidate is the strict minimizer.
-/

/-! ## Part 5: Main Stability Theorem -/

/-
**Elimination-order stability theorem.** If the elimination of `v` on `S`
    is gap-certified with parameter `γ`, and `v'` is within `ε` of `v`
    coordinatewise with `2ε < γ`, then the elimination order of `v'` on `S`
    equals that of `v`.
-/

/-! ## Part 6: Winner Stability -/

/-
**Winner stability theorem.** Under the same hypotheses as
    `eliminationOrderOn_stable`, the IRV winner is preserved.
-/

/-
Winner stability on the full candidate set.
-/

/-! ## Part 7: Tropical / GL3 Certified Robustness Corollary -/

/-
**Tropical/GL3 certified robustness theorem.** If a score map `s` is
    K-Lipschitz in L∞ (in the sense that coordinatewise perturbation ≤ r
    implies score perturbation ≤ K*r), and the elimination of `s x` on all
    candidates is gap-certified with parameter `γ`, then any input `x'`
    within L∞-radius `r` of `x` yields the same IRV winner, provided
    `2 K r < γ`.
-/

end IRV



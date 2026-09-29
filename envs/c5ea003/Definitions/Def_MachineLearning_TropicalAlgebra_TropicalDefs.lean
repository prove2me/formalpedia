-- Prove2me | Definitions.Def_MachineLearning_TropicalAlgebra_TropicalDefs
-- name    : MachineLearning_TropicalAlgebra_TropicalDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:03.030205+00:00
-- url     : https://prove2.me/theorems/c72c2db9-a21d-4d4d-b688-b8d4401d5b9a
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalAlgebra_TropicalDefs
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalAlgebra.TropicalDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalAlgebra/TropicalDefs.lean by skeleton subtraction
import Mathlib
/-
# Tropical Certified Robustness — Core Definitions and Per-Expert Lemmas

This module formalizes the core definitions for multiclass piecewise-linear
network robustness certification via logit-gap margins, and proves the
key analytic lemma: a positive score gap combined with a coordinatewise
Lipschitz bound implies decision stability under L∞ perturbation.
-/

open Finset BigOperators Classical

noncomputable section

attribute [local instance] Classical.propDecidable

variable {n C d : ℕ} [NeZero C]

/-! ## Core Definitions -/

/-- A score vector `s` *decides* class `c` if `c` achieves the maximum score. -/
def decides (s : Fin C → ℝ) (c : Fin C) : Prop :=
  ∀ j : Fin C, s j ≤ s c

/-- Strict version: `c` is the unique maximizer. -/
def StrictDecides (s : Fin C → ℝ) (c : Fin C) : Prop :=
  ∀ j : Fin C, j ≠ c → s j < s c

/-- `StrictDecides` implies `decides`. -/
theorem StrictDecides.decides {s : Fin C → ℝ} {c : Fin C}
    (h : StrictDecides s c) : decides s c := by
  intro j
  by_cases hj : j = c
  · subst hj; exact le_refl _
  · exact le_of_lt (h j hj)


/-- Helper to produce the nonemptiness witness for `univ.erase c` when `C ≥ 2`. -/
theorem erase_univ_nonempty (hC : 1 < C) (c : Fin C) :
    (Finset.univ (α := Fin C) |>.erase c).Nonempty := by
  have : Nontrivial (Fin C) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Finset.erase_nonempty (Finset.mem_univ c)]
  exact Finset.univ_nontrivial

/-- The score gap of class `c`: the margin by which `c` beats the runner-up. -/
def scoreGap (f : (Fin d → ℝ) → Fin C → ℝ) (x : Fin d → ℝ) (c : Fin C)
    (hC : 1 < C) : ℝ :=
  f x c - Finset.sup' (Finset.univ.erase c) (erase_univ_nonempty hC c) (fun j => f x j)

/-- Vote count: number of experts predicting class `c` at input `x`. -/
def voteCount (F : Fin n → (Fin d → ℝ) → Fin C → ℝ) (x : Fin d → ℝ) (c : Fin C) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => decides (F i x) c)).card

/-- The set of experts that vote for class `c` at input `x`. -/
def winnerVoters (F : Fin n → (Fin d → ℝ) → Fin C → ℝ) (x : Fin d → ℝ) (c : Fin C) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => decides (F i x) c)


/-- L∞ ball predicate. -/
def InLInfBall (x z : Fin d → ℝ) (r : ℝ) : Prop :=
  ∀ k, |z k - x k| ≤ r

/-- Coordinatewise Lipschitz bound. -/
def CoordLipschitz (f : (Fin d → ℝ) → Fin C → ℝ) (K : ℝ) : Prop :=
  ∀ x z c, |f z c - f x c| ≤ K * (∑ k : Fin d, |z k - x k|)

/-! ## Key Analytic Lemma: L∞ ball sum bound -/

/-
Sum of absolute coordinate differences is at most `d * r` on an L∞ ball.
-/

/-! ## Key Analytic Lemma: decision stability under Lipschitz perturbation -/

/-
Auxiliary: Lipschitz bound gives a lower bound on f z c.
-/

/-
Auxiliary: Lipschitz bound gives an upper bound on f z j.
-/

/-
The sup' over `univ.erase c` is at most every element outside `c`.
-/

/-
If the score gap exceeds `2 * K * d * r` and `f` is `K`-Lipschitz,
    then `f` still strictly decides `c` throughout the L∞ ball of radius `r`.
-/



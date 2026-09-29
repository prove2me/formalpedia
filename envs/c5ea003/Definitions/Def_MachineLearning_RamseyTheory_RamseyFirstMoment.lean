-- Prove2me | Definitions.Def_MachineLearning_RamseyTheory_RamseyFirstMoment
-- name    : MachineLearning_RamseyTheory_RamseyFirstMoment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:35.314055+00:00
-- url     : https://prove2.me/theorems/c96b85aa-3006-4adc-8477-8d708a1f9847
-- title:
--   Aether Catalog definitions — MachineLearning_RamseyTheory_RamseyFirstMoment
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.RamseyTheory.RamseyFirstMoment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/RamseyTheory/RamseyFirstMoment.lean by skeleton subtraction
import Mathlib
/-
# First-moment counting for the 3-uniform diagonal hypergraph Ramsey number `R(4,4;3)`

This file formalizes, from scratch and self-containedly, the **first-moment / averaging**
("probabilistic method") lower-bound argument for the 3-uniform diagonal hypergraph Ramsey
number, packaged through an *exact finite counting identity* rather than measure theory.

## Set-up

* `Edge3 n` — the 3-element subsets ("3-edges") of `Fin n`.
* `Quad4 n` — the 4-element subsets ("4-sets") of `Fin n`.
* `Coloring n := Edge3 n → Bool` — a 2-coloring of the 3-edges.
* `MonoOn4 χ Q` — all four 3-edges contained in the 4-set `Q` get the same color.
* `badCount χ` — the number of monochromatic 4-sets of `χ`.

## Pipeline

1. Finite instances are obtained automatically for the subtype representations.
2. Cardinalities: `card_Edge3`, `card_Quad4`, `card_Coloring`.
3. For a fixed 4-set `Q`, the number of colorings with `MonoOn4 χ Q` is
   `2 * 2 ^ (C(n,3) - 4) = 2 ^ (C(n,3) - 3)` (`card_mono_fixed_quad`); the
   "monochromatic probability" is `2 / 2^4 = 1/8`.
4. Exact incidence identity (`sum_badCount`):
   `∑ χ, badCount χ = C(n,4) * 2 ^ (C(n,3) - 3)`.
5. Expectation formula (`expectation_badCount`): the average of `badCount` over the
   uniform finite coloring space equals `C(n,4) / 8`.
6. First-moment existence (`exists_good_of_choose_lt_eight`): whenever the expectation is
   `< 1`, i.e. `C(n,4) < 8`, some coloring has `badCount = 0`.

## IMPORTANT mathematical correction to the requested target

The task statement asks to specialize the argument at `n = 13` and to "prove numerically
that this expectation is `< 1`", concluding `R(4,4;3) > 13`.  **This is mathematically
false.**  The first-moment expectation here is exactly `C(n,4)/8`, so the condition
"expectation `< 1`" is equivalent to `C(n,4) < 8`, which holds only for `n ≤ 5`
(`C(5,4) = 5 < 8`, `C(6,4) = 15`).  For `n = 13` the expectation is
`C(13,4)/8 = 715/8 ≈ 89.4 ≥ 1`, so the first-moment argument yields *nothing* at `n = 13`
(see `expectation_thirteen` and `first_moment_insufficient_thirteen`).

Moreover the conclusion itself is false: the exact value is `R^{(3)}(4,4) = 13`
(McKay–Radziszowski, 1991), meaning **every** 2-coloring of the 3-subsets of a 13-element
set contains a monochromatic tetrahedron; in particular no "good" coloring of `Fin 13`
exists at all, so `R(4,4;3) > 13` cannot be proved by any method.

Accordingly, this file proves the genuinely correct first-moment bound:
`exists_good_coloring_five` / `ramsey_three_four_four_gt_five`, i.e. `R(4,4;3) > 5`,
the strongest diagonal bound the first moment actually delivers, together with the full
exact counting pipeline (steps 1–6) for general `n`.
-/

open Finset

namespace RamseyFirstMoment

/-! ## 1. Types and finite instances -/

/-- The 3-edges of `Fin n`: 3-element subsets. -/
abbrev Edge3 (n : ℕ) : Type := {s : Finset (Fin n) // s.card = 3}

/-- The 4-sets of `Fin n`: 4-element subsets. -/
abbrev Quad4 (n : ℕ) : Type := {s : Finset (Fin n) // s.card = 4}

/-- A 2-coloring of the 3-edges. -/
abbrev Coloring (n : ℕ) : Type := Edge3 n → Bool

/-! ## 2. Cardinality lemmas -/




/-! ## 3. The 3-edges of a 4-set and the monochromatic predicate -/

/-- The four 3-edges contained in a 4-set `Q`. -/
def edgesOf {n : ℕ} (Q : Quad4 n) : Finset (Edge3 n) :=
  Finset.univ.filter (fun e => e.val ⊆ Q.val)



/-- `MonoOn4 χ Q`: all 3-edges contained in `Q` receive the same color under `χ`. -/
def MonoOn4 {n : ℕ} (χ : Coloring n) (Q : Quad4 n) : Prop :=
  ∀ e₁ ∈ edgesOf Q, ∀ e₂ ∈ edgesOf Q, χ e₁ = χ e₂

instance {n : ℕ} (χ : Coloring n) (Q : Quad4 n) : Decidable (MonoOn4 χ Q) := by
  unfold MonoOn4; infer_instance

/-- The number of monochromatic 4-sets of a coloring. -/
def badCount {n : ℕ} (χ : Coloring n) : ℕ :=
  (Finset.univ.filter (fun Q : Quad4 n => MonoOn4 χ Q)).card

/-! ## General function-counting lemmas -/

/-- Bijection: functions `α → Bool` agreeing with the constant `c` on `S` are determined
by their values off `S`. -/
def constEquiv {α : Type*} [DecidableEq α] (S : Finset α) (c : Bool) :
    {f : α → Bool // ∀ a ∈ S, f a = c} ≃ ({a : α // a ∉ S} → Bool) where
  toFun f a := f.1 a.1
  invFun g := ⟨fun a => if h : a ∈ S then c else g ⟨a, h⟩, by intro a ha; simp [ha]⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext a
    by_cases h : a ∈ S
    · simp [h, hf a h]
    · simp [h]
  right_inv := by
    intro g
    funext a
    simp [a.2]

/-
The number of functions `α → Bool` that take a *fixed* value `c` on `S` is
`2 ^ (|α| - |S|)`.
-/

/-
The number of functions `α → Bool` that are *constant* on a nonempty `S` is
`2 * 2 ^ (|α| - |S|)`.
-/

/-! ## 3'. Count of colorings making a fixed 4-set monochromatic -/


/-! ## 4. The exact incidence identity -/


/-! ## 5. The expectation formula -/


/-! ## 6. First-moment existence -/


/-! ## 7–8. The correct specialization: `R(4,4;3) > 5` -/



/-! ## The honest situation at `n = 13` -/



end RamseyFirstMoment



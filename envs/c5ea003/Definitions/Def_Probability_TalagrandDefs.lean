-- Prove2me | Definitions.Def_Probability_TalagrandDefs
-- name    : Probability_TalagrandDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:58.983708+00:00
-- url     : https://prove2.me/theorems/493aaf0b-fc99-4601-bc27-fef0311eb770
-- title:
--   Aether Catalog definitions — Probability_TalagrandDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandDefs.lean by skeleton subtraction
import Mathlib

/-!
# Talagrand's convex distance on finite product spaces: definitions

This file sets up the combinatorial/geometric objects underlying Talagrand's
concentration inequality on product spaces.

Throughout, the ambient space is the finite product `Fin n → α` for a finite
alphabet `α`.  For a subset `A` (a `Finset`) and a point `x`, Talagrand's
*convex distance* is

  `d_T(x, A) = min { ‖v‖₂ : v ∈ conv { (1[x i ≠ y i])_i : y ∈ A } }`.

Rather than invoking `convexHull`, we encode a point of the convex hull by an
explicit finite convex combination (`Talagrand.IsRep`), which makes the
inductive proof of the concentration inequality far more manageable.  We work
throughout with the *square* of the convex distance, `Talagrand.dTsq`, since
this is the quantity that appears in the exponential moment bound.

## Main definitions

* `Talagrand.hamm` — the one-coordinate Hamming indicator.
* `Talagrand.IsRep A x v` — `v` is a convex combination of the Hamming
  indicator vectors `y ↦ (1[x i ≠ y i])_i` for `y ∈ A`.
* `Talagrand.sqn` — the squared Euclidean norm on `Fin n → ℝ`.
* `Talagrand.dTsq A x` — the squared convex distance from `x` to `A`.
* `Talagrand.dHamming w A x` — the `w`-weighted Hamming distance from `x` to `A`.

## Main results

* `Talagrand.dTsq_nonneg`, `Talagrand.dTsq_le_of_isRep`, `Talagrand.exists_isRep_lt`
  — the basic infimum API.
* `Talagrand.dTsq_eq_zero_of_mem`, `Talagrand.dTsq_le_card` — degenerate bounds.
* `Talagrand.dTsq_mono` — antitonicity in the target set.
* `Talagrand.dHamming_sq_le_dTsq` — the duality inequality: the convex distance
  dominates every weighted Hamming distance with `∑ w i ^ 2 ≤ 1`.  This is the
  easy (Cauchy–Schwarz) half of Talagrand's minimax description of `d_T`, and
  it is exactly the half needed to derive weighted-Hamming concentration.
-/

namespace Talagrand

open Finset

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- The Hamming indicator of a single coordinate: `0` if the letters agree,
`1` otherwise. -/
def hamm (u v : α) : ℝ := if u = v then 0 else 1




/-- The squared Euclidean norm. -/
def sqn (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2


/-- `v` is a convex combination of the Hamming indicator vectors of the points
of `A`, as seen from `x`. -/
def IsRep (A : Finset (Fin n → α)) (x : Fin n → α) (v : Fin n → ℝ) : Prop :=
  ∃ (k : ℕ) (w : Fin k → ℝ) (y : Fin k → (Fin n → α)),
    (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ (∀ j, y j ∈ A) ∧
    ∀ i, v i = ∑ j, w j * hamm (x i) (y j i)



/-- The squared convex distance of Talagrand. -/
noncomputable def dTsq (A : Finset (Fin n → α)) (x : Fin n → α) : ℝ :=
  sInf {s : ℝ | ∃ v, IsRep A x v ∧ s = sqn v}










/-- The `w`-weighted Hamming distance from `x` to the set `A`. -/
noncomputable def dHamming (w : Fin n → ℝ) (A : Finset (Fin n → α)) (x : Fin n → α) : ℝ :=
  sInf {t : ℝ | ∃ y ∈ A, t = ∑ i, w i * hamm (x i) (y i)}





end Talagrand



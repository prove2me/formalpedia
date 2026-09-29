-- Prove2me | Definitions.Def_Probability_TalagrandRep
-- name    : Probability_TalagrandRep
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:39.716741+00:00
-- url     : https://prove2.me/theorems/ab08a4bc-e778-4ec0-afe3-8fc92474e3c6
-- title:
--   Aether Catalog definitions — Probability_TalagrandRep
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandRep`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandRep.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TalagrandDefs

/-!
# Weight-function representations of the convex distance

`Talagrand.IsRep` encodes a point of Talagrand's convex hull by an *indexed
family* of points of `A` together with convex weights.  For the inductive proof
of the concentration inequality it is far more convenient to index the convex
combination by the finite set `A` itself.  This file introduces that variant,
`Talagrand.IsRepW`, proves it equivalent to `Talagrand.IsRep`, and repackages
the basic `dTsq` API in terms of it.

## Main results

* `Talagrand.isRepW_iff_isRep` — the two encodings of the convex hull agree.
* `Talagrand.dTsq_le_of_isRepW` — a weight function bounds `dTsq` from above.
* `Talagrand.exists_isRepW_lt` — near-optimal weight representations exist.
-/

namespace Talagrand

open Finset

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- A convex combination of the Hamming indicator vectors of the points of `A`,
indexed by `A` itself: `w` is a probability weight on `A`. -/
def IsRepW (A : Finset (Fin n → α)) (x : Fin n → α) (v : Fin n → ℝ) : Prop :=
  ∃ w : (Fin n → α) → ℝ, (∀ z, 0 ≤ w z) ∧ (∑ z ∈ A, w z = 1) ∧
    ∀ i, v i = ∑ z ∈ A, w z * hamm (x i) (z i)






end Talagrand



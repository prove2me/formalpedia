-- Prove2me | Definitions.Def_Probability_TalagrandIsoperimetry
-- name    : Probability_TalagrandIsoperimetry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:17.644332+00:00
-- url     : https://prove2.me/theorems/f8e3139b-63b1-461a-b9bb-778a5a0cd9fe
-- title:
--   Aether Catalog definitions — Probability_TalagrandIsoperimetry
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandIsoperimetry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandIsoperimetry.lean by skeleton subtraction
import Mathlib

/-!
# Convex-distance isoperimetry, and the exact convex distance to a subcube

Two complements to the concentration package.

* `Talagrand.convex_isoperimetry` — the isoperimetric reading of Talagrand's
  inequality: if `A` carries at least half of the mass then the complement of its
  `t`-neighbourhood *for the convex distance* has mass at most `2 exp (-t/4)`.
* `Talagrand.dTsq_cylinder` — the convex distance to a **subcube** (a cylinder set
  `{y | ∀ i ∈ B, y i = c i}`) is computed *exactly*: it is the number of
  coordinates of `B` on which `x` disagrees with the pattern `c`.  Together with
  `Talagrand.dTsq_singleton` (the case `B = univ`) this shows that the general
  bound is attained on a family of sets of arbitrary size, so the exponent in the
  isoperimetric bound cannot be improved by a change of the geometry alone.
* `Talagrand.cylinder_concentration` — the resulting explicit deviation bound for
  subcubes, in which the convex distance has been eliminated in favour of a
  coordinate count.
-/

namespace Talagrand

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}


/-- The cylinder (subcube) of points following the pattern `c` on the coordinates
of `B`. -/
def cylinder (B : Finset (Fin n)) (c : Fin n → α) : Finset (Fin n → α) :=
  Finset.univ.filter (fun y => ∀ i ∈ B, y i = c i)





end Talagrand



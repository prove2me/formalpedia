-- Prove2me | Theorems.Thm_Talagrand_dTsq_cylinder
-- name    : Talagrand.dTsq_cylinder
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:10:16.307683+00:00
-- url     : https://prove2.me/theorems/5582858b-32c0-4184-97ff-62ad1b12db3c
-- title:
--   The convex distance to a subcube, exactly.
-- statement:
--   **The convex distance to a subcube, exactly.**  For the cylinder fixing the
--   coordinates of `B` to the pattern `c`, the squared convex distance from `x` is the
--   number of coordinates of `B` on which `x` disagrees with `c`.
--
--   ```lean
--   theorem Talagrand.dTsq_cylinder(B : Finset (Fin n)) (c x : Fin n → α) :
--       dTsq (cylinder B c) x = ((B.filter (fun i => x i ≠ c i)).card : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TalagrandIsoperimetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TalagrandIsoperimetry.lean#L54

-- Thm stub generated from Probability/TalagrandIsoperimetry.lean
import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandIsoperimetry

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

open Talagrand

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

theorem Talagrand.dTsq_cylinder(B : Finset (Fin n)) (c x : Fin n → α) :
    dTsq (cylinder B c) x = ((B.filter (fun i => x i ≠ c i)).card : ℝ) := by sorry

-- Prove2me | Theorems.Thm_TropicalConeHull_dependence_of_helly
-- name    : TropicalConeHull.dependence_of_helly
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:21.254707+00:00
-- url     : https://prove2.me/theorems/60c2b9a1-824b-4922-b98a-1a5a35b69619
-- title:
--   Tropical Helly implies tropical dependence.
-- statement:
--   **Tropical Helly implies tropical dependence.**  If in dimension `d` every
--   family of `d + 1` tropical cones whose `d`-element subfamilies intersect has a
--   common point, then any `d + 1` points of `ℝ^d` are tropically dependent.
--   Combined with `TropicalDependence.trop_dependence_fin` (which yields the Helly
--   theorem in `HellyNumber.lean`), tropical Helly and tropical dependence are
--   equivalent statements.
--
--   ```lean
--   theorem TropicalConeHull.dependence_of_helly(hd : 0 < d)
--       (helly : ∀ C : Fin (d + 1) → Set (Fin d → ℝ), (∀ k, IsTropCone (C k)) →
--         (∀ I : Finset (Fin (d + 1)), I.card ≤ d → ∃ x, ∀ k ∈ I, x ∈ C k) →
--         ∃ x, ∀ k, x ∈ C k)
--       (p : Fin (d + 1) → Fin d → ℝ) :
--       ∃ lam : Fin (d + 1) → ℝ, ∀ (i : Fin d) (k : Fin (d + 1)),
--         ∃ j, j ≠ k ∧ lam k + p k i ≤ lam j + p j i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalConvexity/ConeHullOptimization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalConvexity/ConeHullOptimization.lean#L207

-- Thm stub generated from Tropical/TropicalConvexity/ConeHullOptimization.lean
import Mathlib
import Definitions.Def_Tropical_TropicalConvexity_ConeHullOptimization

/-!
# Tropical cone hulls, Carathéodory number `d`, and max-plus residuation

This file complements the tropical Helly theory with the two other pillars of
tropical convexity: the **Carathéodory number** of tropical cones in `ℝ^d`
(which is `d`, one better than the affine normalized bound `d + 1`), and the
**optimization side**: the residuation (Galois) correspondence for max-plus
linear systems, giving the greatest subsolution of `A ⊗ x ≤ b` together with a
complete solvability criterion for `A ⊗ x = b`.

## Main results

* `TropicalConeHull.tropical_caratheodory_cone` — Carathéodory number `d`.
* `TropicalConeHull.caratheodory_cone_sharp` — the bound `d` cannot be improved.
* `TropicalConeHull.colorful_caratheodory` — colourful Carathéodory theorem.
* `TropicalConeHull.dependence_of_helly` — the converse implication
  "tropical Helly ⇒ tropical Cramer dependence", so that the Helly theorem of
  `HellyNumber.lean` and the dependence theorem behind it are *equivalent*.
* `TropicalResiduation.mulVec_le_iff_le_resid` — the residuation Galois
  connection for max-plus linear inequalities.
* `TropicalResiduation.tropical_solvable_iff` — `A ⊗ x = b` is solvable iff the
  canonical candidate `resid A b` solves it (Cuninghame-Green's principal
  solution): an `O(mn)` decision procedure for max-plus linear systems.
-/

open Finset

open TropicalConeHull

variable {d : ℕ} {ι : Type*}






/-! ## The tropical Helly property is *equivalent* to tropical dependence

`HellyNumber.lean` proves the implication "Cramer dependence ⇒ tropical Helly".
Here we close the loop: the Helly property, taken as a hypothesis, forces
`d + 1` points of `ℝ^d` to be tropically dependent.  So the two statements are
two faces of the same phenomenon. -/

theorem TropicalConeHull.dependence_of_helly(hd : 0 < d)
    (helly : ∀ C : Fin (d + 1) → Set (Fin d → ℝ), (∀ k, IsTropCone (C k)) →
      (∀ I : Finset (Fin (d + 1)), I.card ≤ d → ∃ x, ∀ k ∈ I, x ∈ C k) →
      ∃ x, ∀ k, x ∈ C k)
    (p : Fin (d + 1) → Fin d → ℝ) :
    ∃ lam : Fin (d + 1) → ℝ, ∀ (i : Fin d) (k : Fin (d + 1)),
      ∃ j, j ≠ k ∧ lam k + p k i ≤ lam j + p j i := by sorry

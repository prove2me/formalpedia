-- Prove2me | Theorems.Thm_TropicalConeHull_tropical_caratheodory_cone
-- name    : TropicalConeHull.tropical_caratheodory_cone
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:28.06792+00:00
-- url     : https://prove2.me/theorems/29999019-409c-4ce0-a201-18a4b152daf5
-- title:
--   Tropical Carathéodory theorem for cones (Carathéodory number `d`).
-- statement:
--   **Tropical Carathéodory theorem for cones (Carathéodory number `d`).**
--   Every point of the tropical cone hull of a finite family in `ℝ^d` already lies
--   in the hull of at most `d` of the generators — one generator per coordinate.
--
--   ```lean
--   theorem TropicalConeHull.tropical_caratheodory_cone(hd : 0 < d) (p : ι → Fin d → ℝ)
--       (F : Finset ι) (z : Fin d → ℝ) (hz : z ∈ tropConeHull p F) :
--       ∃ G ⊆ F, G.card ≤ d ∧ z ∈ tropConeHull p G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalConvexity/ConeHullOptimization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalConvexity/ConeHullOptimization.lean#L45

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

theorem TropicalConeHull.tropical_caratheodory_cone(hd : 0 < d) (p : ι → Fin d → ℝ)
    (F : Finset ι) (z : Fin d → ℝ) (hz : z ∈ tropConeHull p F) :
    ∃ G ⊆ F, G.card ≤ d ∧ z ∈ tropConeHull p G := by sorry

-- Prove2me | Theorems.Thm_TropicalConeHull_caratheodory_cone_sharp
-- name    : TropicalConeHull.caratheodory_cone_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:13.563108+00:00
-- url     : https://prove2.me/theorems/a91f7410-46c1-4577-8c63-5dc5aef01aeb
-- title:
--   Sharpness of the tropical Carathéodory number.
-- statement:
--   **Sharpness of the tropical Carathéodory number.**  The `d` "tropical unit
--   vectors" of `ℝ^d` span a point of their cone hull that lies in the hull of no
--   proper subfamily.  Hence the Carathéodory number of tropical cones in `ℝ^d` is
--   exactly `d`.
--
--   ```lean
--   theorem TropicalConeHull.caratheodory_cone_sharp(hd : 0 < d) :
--       ∃ (p : Fin d → Fin d → ℝ) (z : Fin d → ℝ),
--         z ∈ tropConeHull p univ ∧
--         ∀ G : Finset (Fin d), G.card < d → z ∉ tropConeHull p G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalConvexity/ConeHullOptimization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalConvexity/ConeHullOptimization.lean#L73

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

theorem TropicalConeHull.caratheodory_cone_sharp(hd : 0 < d) :
    ∃ (p : Fin d → Fin d → ℝ) (z : Fin d → ℝ),
      z ∈ tropConeHull p univ ∧
      ∀ G : Finset (Fin d), G.card < d → z ∉ tropConeHull p G := by sorry

-- Prove2me | Theorems.Thm_TropicalConeHull_colorful_caratheodory
-- name    : TropicalConeHull.colorful_caratheodory
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:21.122777+00:00
-- url     : https://prove2.me/theorems/130f0263-5a4b-4484-adfe-7cce2eada115
-- title:
--   Tropical colourful Carathéodory theorem.
-- statement:
--   **Tropical colourful Carathéodory theorem.**  If a point `z` lies in the
--   tropical cone hull of each of `d` "colour classes" of points of `ℝ^d`, then it
--   lies in the hull of a *rainbow* selection — one generator taken from each class.
--   The selection is explicit: from class `c` take a generator attaining the maximum
--   in coordinate `c`.
--
--   ```lean
--   theorem TropicalConeHull.colorful_caratheodory(hd : 0 < d) (p : Fin d → ι → Fin d → ℝ)
--       (F : Fin d → Finset ι) (z : Fin d → ℝ)
--       (hz : ∀ c, z ∈ tropConeHull (p c) (F c)) :
--       ∃ (sel : Fin d → ι) (w : Fin d → ℝ), (∀ c, sel c ∈ F c) ∧
--         ∀ i, z i = (univ : Finset (Fin d)).sup'
--           ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun c => w c + p c (sel c) i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalConvexity/ConeHullOptimization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalConvexity/ConeHullOptimization.lean#L117

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

theorem TropicalConeHull.colorful_caratheodory(hd : 0 < d) (p : Fin d → ι → Fin d → ℝ)
    (F : Fin d → Finset ι) (z : Fin d → ℝ)
    (hz : ∀ c, z ∈ tropConeHull (p c) (F c)) :
    ∃ (sel : Fin d → ι) (w : Fin d → ℝ), (∀ c, sel c ∈ F c) ∧
      ∀ i, z i = (univ : Finset (Fin d)).sup'
        ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun c => w c + p c (sel c) i) := by sorry

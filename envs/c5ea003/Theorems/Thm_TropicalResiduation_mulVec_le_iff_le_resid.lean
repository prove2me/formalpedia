-- Prove2me | Theorems.Thm_TropicalResiduation_mulVec_le_iff_le_resid
-- name    : TropicalResiduation.mulVec_le_iff_le_resid
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:40:10.395132+00:00
-- url     : https://prove2.me/theorems/6e52cd7b-78b4-4d0f-a93a-06152bf33aba
-- title:
--   Residuation (Galois connection).
-- statement:
--   **Residuation (Galois connection).**  `A ⊗ x ≤ b` holds if and only if
--   `x ≤ A ♯ b` coordinatewise.  Thus `A ♯ b` is the greatest subsolution.
--
--   ```lean
--   theorem TropicalResiduation.mulVec_le_iff_le_resid(A : Fin (m + 1) → Fin (n + 1) → ℝ)
--       (b : Fin (m + 1) → ℝ) (x : Fin (n + 1) → ℝ) :
--       (∀ i, mulVec A x i ≤ b i) ↔ (∀ j, x j ≤ resid A b j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalConvexity/ConeHullOptimization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalConvexity/ConeHullOptimization.lean#L293

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







open TropicalResiduation

variable {m n : ℕ}

theorem TropicalResiduation.mulVec_le_iff_le_resid(A : Fin (m + 1) → Fin (n + 1) → ℝ)
    (b : Fin (m + 1) → ℝ) (x : Fin (n + 1) → ℝ) :
    (∀ i, mulVec A x i ≤ b i) ↔ (∀ j, x j ≤ resid A b j) := by sorry

-- Prove2me | Theorems.Thm_eventual_image_eq_fixed_points
-- name    : eventual_image_eq_fixed_points
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:31:09.055672+00:00
-- url     : https://prove2.me/theorems/e6bd0a8e-e9d4-45b0-9fb1-4d90d47427c2
-- title:
--   The eventual image of a monotone descending map equals the set of fixed points.
-- statement:
--   The eventual image of a monotone descending map equals the set of fixed points.
--
--   ```lean
--   theorem eventual_image_eq_fixed_points    {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]
--       (F : P → P)
--       (hmono : Monotone F)
--       (hdesc : ∀ x : P, F x ≤ x) :
--       Set.range (F^[Fintype.card P]) = {x | F x = x} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GardenOfEden.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GardenOfEden.lean#L130

-- Thm stub generated from Bridges/GardenOfEden.lean
import Mathlib
import Definitions.Def_Bridges_GardenOfEden
/-
# Finite Garden-of-Eden Principle

A formal treatment of the Garden-of-Eden theorem for finite dynamical systems,
establishing that non-surjective dynamics on finite state spaces produce
permanently unreachable ("Garden-of-Eden") configurations, and that monotone
descending maps on finite partial orders stabilize in bounded time.

## Main Results

- `iterate_descends`: Iterates of a descending map form a descending chain.
- `finite_garden_of_eden_descent`: Every orbit of a monotone descending map on a
  finite partial order stabilizes within `Fintype.card P` steps.
- `finite_garden_of_eden_of_not_surjective`: A non-surjective monotone descending map
  has a Garden-of-Eden state outside the eventual image.
- `finite_configuration_garden_of_eden`: On finite configuration spaces, non-surjective
  maps have unreachable configurations.
- `preinjective_of_surjective_on_finite_configurations`: Finite Moore–Myhill shadow —
  surjectivity implies injectivity on finite types.

## Concepts

A **Garden-of-Eden** state is a configuration with no preimage under the dynamics.
The **eventual image** is the range of sufficiently many iterates.
**Descent-stabilization** means every orbit reaches a fixed point in bounded time.
-/


open Function Set

theorem eventual_image_eq_fixed_points    {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]
    (F : P → P)
    (hmono : Monotone F)
    (hdesc : ∀ x : P, F x ≤ x) :
    Set.range (F^[Fintype.card P]) = {x | F x = x} := by sorry

-- Prove2me | Definitions.Def_Bridges_GardenOfEden
-- name    : Bridges_GardenOfEden
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:07.397211+00:00
-- url     : https://prove2.me/theorems/92bb0072-56a1-43e8-896f-dbd871927d8d
-- title:
--   Aether Catalog definitions — Bridges_GardenOfEden
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GardenOfEden`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GardenOfEden.lean by skeleton subtraction
import Mathlib
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

/-- A Garden-of-Eden state for `F` is one with no preimage. -/
def IsGardenOfEden {α : Type*} (F : α → α) (y : α) : Prop :=
  ∀ x, F x ≠ y



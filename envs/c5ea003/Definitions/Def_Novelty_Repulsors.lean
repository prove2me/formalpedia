-- Prove2me | Definitions.Def_Novelty_Repulsors
-- name    : Novelty_Repulsors
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:39:26.051507+00:00
-- url     : https://prove2.me/theorems/a894147b-9abe-46e9-ac74-d57977b52d49
-- title:
--   Aether Catalog definitions — Novelty_Repulsors
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Repulsors`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Repulsors.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.Other.Repulsors

Auto-generated from theorem catalog database.
Domain: Speculative/Other
Declarations: 16
-/

noncomputable section

/-- A discrete-time dynamical system. -/
structure DiscreteDynSystem (α : Type*) where
  step : α → α

/-- The n-th iterate of a discrete dynamical system. -/
def DiscreteDynSystem.iterate {α : Type*} (ds : DiscreteDynSystem α) : ℕ → α → α
  | 0 => id
  | n + 1 => ds.step ∘ ds.iterate n



/-- A fixed point of a discrete dynamical system. -/
def DiscreteDynSystem.IsFixedPoint {α : Type*} (ds : DiscreteDynSystem α) (x : α) : Prop :=
  ds.step x = x



/-- A set is a repulsor if nearby orbits Filter.eventually leave every neighborhood. -/
def IsDiscreteRepulsor {α : Type*} [PseudoMetricSpace α] (ds : DiscreteDynSystem α)
    (R : Set α) : Prop :=
  ∃ U : Set α, IsOpen U ∧ R ⊆ U ∧
    ∀ x ∈ U \ R, ∃ n : ℕ, ds.iterate n x ∉ U



/-- A bijective discrete dynamical system. -/
structure BijectiveDynSystem (α : Type*) extends DiscreteDynSystem α where
  inv : α → α
  left_inv : ∀ x, inv (step x) = x
  right_inv : ∀ x, step (inv x) = x






end



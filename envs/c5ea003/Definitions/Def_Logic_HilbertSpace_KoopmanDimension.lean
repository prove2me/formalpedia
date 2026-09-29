-- Prove2me | Definitions.Def_Logic_HilbertSpace_KoopmanDimension
-- name    : Logic_HilbertSpace_KoopmanDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:27.003984+00:00
-- url     : https://prove2.me/theorems/31de431c-6009-44f4-b2ff-34cfa5db8eb7
-- title:
--   Aether Catalog definitions — Logic_HilbertSpace_KoopmanDimension
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.HilbertSpace.KoopmanDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/HilbertSpace/KoopmanDimension.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.MachineLearning.KoopmanDimension

Auto-generated from theorem catalog database.
Domain: MachineLearning
Declarations: 20
-/


noncomputable section

/-- Koopman operator: lifts dynamics f to act on observables. -/
def KoopmanLift {X : Type*} (f : X → X) (g : X → ℝ) : X → ℝ := g ∘ f




































/-- Equivariance definition for dynamics. -/
def IsEquivKoop {X : Type*} (f σ : X → X) : Prop :=
  ∀ x, f (σ x) = σ (f x)












































end



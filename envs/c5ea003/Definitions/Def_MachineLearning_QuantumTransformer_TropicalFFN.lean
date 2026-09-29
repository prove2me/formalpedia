-- Prove2me | Definitions.Def_MachineLearning_QuantumTransformer_TropicalFFN
-- name    : MachineLearning_QuantumTransformer_TropicalFFN
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:12.136493+00:00
-- url     : https://prove2.me/theorems/d4aa2d3d-80fd-4365-ade8-ca98b340a8db
-- title:
--   Aether Catalog definitions — MachineLearning_QuantumTransformer_TropicalFFN
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.QuantumTransformer.TropicalFFN`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/QuantumTransformer/TropicalFFN.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.MachineLearning.QuantumTransformer.TropicalFFN

Auto-generated from theorem catalog database.
Domain: MachineLearning/QuantumTransformer
Declarations: 11
-/


noncomputable section

















/-- The crystallization loss for a ReLU neuron: small when |x| is large. -/
def relu_crystal_loss (x : ℝ) : ℝ := 1 / (1 + x ^ 2)
















def is_tropical_monomial (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x, f x = a * x + b












end



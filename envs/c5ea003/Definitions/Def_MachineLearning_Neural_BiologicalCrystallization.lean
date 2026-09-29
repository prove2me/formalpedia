-- Prove2me | Definitions.Def_MachineLearning_Neural_BiologicalCrystallization
-- name    : MachineLearning_Neural_BiologicalCrystallization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:49.326648+00:00
-- url     : https://prove2.me/theorems/1a497967-d620-4afb-a325-ed6cd1ad7f3e
-- title:
--   Aether Catalog definitions — MachineLearning_Neural_BiologicalCrystallization
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.Neural.BiologicalCrystallization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/Neural/BiologicalCrystallization.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.MachineLearning.QuantumTransformer.BiologicalCrystallization

Auto-generated from theorem catalog database.
Domain: MachineLearning/QuantumTransformer
Declarations: 13
-/


noncomputable section

/-- [Section: # CatalogBuild.MachineLearning.QuantumTransformer.BiologicalCrystallization
Auto-generated from theorem catalog database.
Domain: MachineLearning/QuantumTransformer
Declarations: 13] -/
def is_one_hot {n : ℕ} (v : Fin n → ℝ) : Prop :=
  ∃ k, v k = 1 ∧ ∀ j, j ≠ k → v j = 0
















def is_k_sparse {n : ℕ} (k : ℕ) (v : Fin n → ℝ) : Prop :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ k




























/-- The order parameter for crystallization. -/
def order_parameter {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (1 / ↑n) * ∑ i, w i * (1 - w i)








end



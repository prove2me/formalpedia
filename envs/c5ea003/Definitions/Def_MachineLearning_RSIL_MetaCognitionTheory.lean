-- Prove2me | Definitions.Def_MachineLearning_RSIL_MetaCognitionTheory
-- name    : MachineLearning_RSIL_MetaCognitionTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:18.138626+00:00
-- url     : https://prove2.me/theorems/4717d765-2a0b-4613-8016-9f0b3165586f
-- title:
--   Aether Catalog definitions — MachineLearning_RSIL_MetaCognitionTheory
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.RSIL.MetaCognitionTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/RSIL/MetaCognitionTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.MachineLearning.RSIL.MetaCognitionTheory

Auto-generated from theorem catalog database.
Domain: MachineLearning/RSIL
Declarations: 19
-/


noncomputable section

/-- Meta-cognitive error: absolute difference between estimated and actual performance. -/
def metaCogError (estimated actual : ℝ) : ℝ := |estimated - actual|


/-- A system is ε-calibrated if its self-assessment error is at most ε. -/
def Calibrated (estimated actual ε : ℝ) : Prop :=
  metaCogError estimated actual ≤ ε


/-- Improvement potential: gap between achievable and actual performance. -/
def improvementPotential (achievable actual : ℝ) : ℝ := achievable - actual


/-- Exploration-exploitation value: weighted combination. -/
def explorationValue (exploit explore uncertainty weight : ℝ) : ℝ :=
  exploit + weight * uncertainty * explore


/-- Overconfidence: max(0, estimated - actual). -/
def overconfidence (estimated actual : ℝ) : ℝ := max 0 (estimated - actual)


/-- Cost of self-evaluation for a model with given parameters. -/
def selfEvalCost (params : ℕ) (baseCost : ℝ) : ℝ := baseCost * Real.sqrt (params : ℝ)


/-- Meta-learning rate: convergence of meta-learning toward base rate. -/
def metaLearningRate (baseRate : ℝ) (n : ℕ) : ℝ := baseRate * (1 - 1 / (n + 1 : ℝ))


/-- Standard parameter count. -/
def metaStandardParams (d : ℕ) : ℕ := d * d


/-- EML parameter count. -/
def metaEmlParams (d : ℕ) : ℕ := 4 * d






















end



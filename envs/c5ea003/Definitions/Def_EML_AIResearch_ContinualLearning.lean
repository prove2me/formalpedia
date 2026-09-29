-- Prove2me | Definitions.Def_EML_AIResearch_ContinualLearning
-- name    : EML_AIResearch_ContinualLearning
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:20:45.184009+00:00
-- url     : https://prove2.me/theorems/fe8cfe12-9b51-4646-841c-123db19f0433
-- title:
--   Aether Catalog definitions — EML_AIResearch_ContinualLearning
-- statement:
--   Definition bundle for the Aether Catalog module `EML.AIResearch.ContinualLearning`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/AIResearch/ContinualLearning.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.AIResearch.ContinualLearning

Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 16
-/

noncomputable section

/-- [Section: # CatalogBuild.EML.AIResearch.ContinualLearning
Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 16] -/
def standardForgetting (overlap : ℝ) (taskDifficulty : ℕ) : ℝ :=
  overlap * ↑taskDifficulty

/-- [Section: # CatalogBuild.EML.AIResearch.ContinualLearning
Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 16] -/
def emlForgetting (overlap invertibilityFactor : ℝ) (taskDifficulty : ℕ) : ℝ :=
  overlap * (1 - invertibilityFactor) * ↑taskDifficulty


def ewcPenalty (fisher paramShift : ℝ) : ℝ := fisher * paramShift ^ 2

def emlEWCCost (d w : ℕ) (avgFisher avgShift : ℝ) : ℝ :=
  ↑(4 * d * w) * ewcPenalty avgFisher avgShift

def stdEWCCost (d w : ℕ) (avgFisher avgShift : ℝ) : ℝ :=
  ↑(d * w * w) * ewcPenalty avgFisher avgShift


def taskCapacity (totalParams paramsPerTask : ℕ) : ℕ := totalParams / paramsPerTask


def replayBufferSize (paramsPerTask numTasks : ℕ) : ℕ := paramsPerTask * numTasks


def emlGrowthCost (newWidth : ℕ) : ℕ := 4 * newWidth

def stdGrowthCost (existingWidth newWidth : ℕ) : ℕ := existingWidth * newWidth


def transferBenefit (sharedFraction : ℝ) (baseCost : ℕ) : ℝ :=
  (1 - sharedFraction) * ↑baseCost


end



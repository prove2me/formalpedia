-- Prove2me | Definitions.Def_EML_AIResearch_RewardModelTheory
-- name    : EML_AIResearch_RewardModelTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:20:54.909199+00:00
-- url     : https://prove2.me/theorems/3a84e591-1427-4411-add9-e3418f805796
-- title:
--   Aether Catalog definitions — EML_AIResearch_RewardModelTheory
-- statement:
--   Definition bundle for the Aether Catalog module `EML.AIResearch.RewardModelTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/AIResearch/RewardModelTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.AIResearch.RewardModelTheory

Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 14
-/

noncomputable section

/-- Standard reward model: LLM backbone + scalar head -/
def stdRewardModelParams (backboneParams headDim : ℕ) : ℕ :=
  backboneParams + headDim

/-- EML reward model -/
def emlRewardModelParams (emlBackboneParams headDim : ℕ) : ℕ :=
  emlBackboneParams + headDim


/-- PPO step cost: forward + backward on policy + reward model evaluation -/
def ppoStepCost (policyParams rewardParams batchSize : ℕ) : ℕ :=
  batchSize * (3 * policyParams + rewardParams)



/-- DPO cost: forward pass on chosen + rejected, no separate reward model -/
def dpoStepCost (policyParams batchSize : ℕ) : ℕ :=
  batchSize * (2 * policyParams)



/-- KL penalty cost: compare policy vs reference model -/
def klPenaltyCost (referenceParams vocabSize seqLen : ℕ) : ℕ :=
  seqLen * (referenceParams + vocabSize)


/-- Total RLHF cost: numRounds × (generation + scoring + update) -/
def rlhfTotalCost (numRounds genCost scoreCost updateCost : ℕ) : ℕ :=
  numRounds * (genCost + scoreCost + updateCost)



end



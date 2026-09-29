-- Prove2me | Definitions.Def_EML_AIResearch_ConstitutionalAITheory
-- name    : EML_AIResearch_ConstitutionalAITheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:20:43.963252+00:00
-- url     : https://prove2.me/theorems/f93845b4-48e2-4a77-9454-962e62b758ef
-- title:
--   Aether Catalog definitions — EML_AIResearch_ConstitutionalAITheory
-- statement:
--   Definition bundle for the Aether Catalog module `EML.AIResearch.ConstitutionalAITheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/AIResearch/ConstitutionalAITheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.AIResearch.ConstitutionalAITheory

Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 13
-/

noncomputable section


/-- Cost of checking all principles for one response -/
def fullCritiqueCost (numPrinciples forwardCost : ℕ) : ℕ :=
  numPrinciples * forwardCost




/-- Full critique-revise cycle -/
def critiqueReviseCost (critCost revCost : ℕ) : ℕ :=
  critCost + revCost


/-- Multiple rounds of critique-revise -/
def multiRoundCAICost (numRounds cycleCost : ℕ) : ℕ :=
  numRounds * cycleCost


/-- RLAIF training: AI-generated preferences + RL update -/
def rlaifCost (numPairs genCost scoreCost updateCost : ℕ) : ℕ :=
  numPairs * (genCost + scoreCost) + updateCost


/-- Full CAI: SL pretraining + critique-revise + RLAIF -/
def caiPipelineCost (pretrainCost crCost rlaifCost : ℕ) : ℕ :=
  pretrainCost + crCost + rlaifCost


end



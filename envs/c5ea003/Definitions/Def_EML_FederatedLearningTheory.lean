-- Prove2me | Definitions.Def_EML_FederatedLearningTheory
-- name    : EML_FederatedLearningTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:27.176907+00:00
-- url     : https://prove2.me/theorems/51e02653-b4bb-4766-a443-96bc4f6cac4c
-- title:
--   Aether Catalog definitions — EML_FederatedLearningTheory
-- statement:
--   Definition bundle for the Aether Catalog module `EML.FederatedLearningTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/FederatedLearningTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.AIResearch.FederatedLearningTheory

Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 20
-/

noncomputable section

/-- Per-round communication: each client sends model updates -/
def commCostPerRound (numClients modelParams bitsPerParam : ℕ) : ℕ :=
  numClients * modelParams * bitsPerParam


/-- Total communication over all rounds -/
def totalCommCost (numRounds numClients modelParams bitsPerParam : ℕ) : ℕ :=
  numRounds * commCostPerRound numClients modelParams bitsPerParam


/-- FedAvg aggregation cost: sum weighted models -/
def aggregationCost (numClients modelParams : ℕ) : ℕ := numClients * modelParams


/-- DP noise magnitude: proportional to sensitivity / epsilon, sensitivity ∝ √params -/
def dpNoiseMagnitude (params : ℝ) (epsilon : ℝ) : ℝ := Real.sqrt params / epsilon



/-- On-device model memory -/
def clientModelMemory (params bitsPerParam : ℕ) : ℕ := params * bitsPerParam


/-- With K out of N clients per round -/
def partialCommCost (activeClients modelParams bitsPerParam : ℕ) : ℕ :=
  activeClients * modelParams * bitsPerParam


/-- Per-client adapter: small personalization layer -/
def stdAdapterParams (d_model d_adapter : ℕ) : ℕ := 2 * d_model * d_adapter

def emlAdapterParams (d_adapter : ℕ) : ℕ := 4 * d_adapter


/-- Secure aggregation: pairwise key exchange + encrypted updates -/
def secureAggCost (numClients modelParams cryptoOverhead : ℕ) : ℕ :=
  numClients * numClients * cryptoOverhead + numClients * modelParams


/-- Compressed gradient communication -/
def compressedGradSize (modelParams comprRatio : ℕ) : ℕ := modelParams / comprRatio


end



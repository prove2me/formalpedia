-- Prove2me | Definitions.Def_Applications_NeuralCoding_LogisticSigmoid_lt_one
-- name    : Applications_NeuralCoding_LogisticSigmoid_lt_one
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:03.368396+00:00
-- url     : https://prove2.me/theorems/af9dc144-1e41-4365-849e-b533891f4373
-- title:
--   Aether Catalog definitions — Applications_NeuralCoding_LogisticSigmoid_lt_one
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NeuralCoding.LogisticSigmoid.lt.one`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NeuralCoding/LogisticSigmoid_lt_one.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.LogisticSigmoid_lt_one

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 6
-/

noncomputable section

/-- The logistic sigmoid function S(x) = eˣ / (1 + eˣ), the derivative of softplus -/
def logisticSigmoid (x : ℝ) : ℝ := Real.exp x / (1 + Real.exp x)






end



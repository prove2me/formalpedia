-- Prove2me | Definitions.Def_Applications_NeuralCoding_LogisticSigmoid
-- name    : Applications_NeuralCoding_LogisticSigmoid
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:53:56.349895+00:00
-- url     : https://prove2.me/theorems/6f195e0a-438a-4c71-9fd3-25abd62b03e1
-- title:
--   Aether Catalog definitions — Applications_NeuralCoding_LogisticSigmoid
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NeuralCoding.LogisticSigmoid`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NeuralCoding/LogisticSigmoid.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.LogisticSigmoid

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 6
-/

noncomputable section

/-- The logistic sigmoid function S(x) = eˣ / (1 + eˣ), the derivative of softplus -/
def logisticSigmoid (x : ℝ) : ℝ := Real.exp x / (1 + Real.exp x)






end



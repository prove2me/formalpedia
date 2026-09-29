-- Prove2me | Definitions.Def_Novelty_NeuralCoding_LogisticSigmoid_lt_one
-- name    : Novelty_NeuralCoding_LogisticSigmoid_lt_one
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:33.772138+00:00
-- url     : https://prove2.me/theorems/ccbc3864-ea0f-4237-b05a-c8a3d979b18b
-- title:
--   Aether Catalog definitions — Novelty_NeuralCoding_LogisticSigmoid_lt_one
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NeuralCoding.LogisticSigmoid.lt.one`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NeuralCoding/LogisticSigmoid_lt_one.lean by skeleton subtraction
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



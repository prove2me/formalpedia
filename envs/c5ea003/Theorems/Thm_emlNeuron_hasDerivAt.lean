-- Prove2me | Theorems.Thm_emlNeuron_hasDerivAt
-- name    : emlNeuron_hasDerivAt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:22:46.708035+00:00
-- url     : https://prove2.me/theorems/76a48990-8f68-402c-aca4-ec970f3a8cf3
-- title:
--   The derivative of the EML neuron.
-- statement:
--   The derivative of the EML neuron.
--   d/dx [exp(w₁x + b₁) − ln(w₂x + b₂)] = w₁·exp(w₁x + b₁) − w₂/(w₂x + b₂).
--
--   ```lean
--   theorem emlNeuron_hasDerivAt(w₁ b₁ w₂ b₂ x : ℝ) (h : w₂ * x + b₂ ≠ 0) :
--       HasDerivAt (fun x' => emlNeuron w₁ b₁ w₂ b₂ x')
--         (w₁ * Real.exp (w₁ * x + b₁) - w₂ / (w₂ * x + b₂)) x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `EML/NeuralCoding/EMLNeuralNetworks.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/EML/NeuralCoding/EMLNeuralNetworks.lean#L43

-- Thm stub generated from EML/SPBExtended/EMLNeuralNetworks.lean
import Mathlib
import Definitions.Def_EML_SPBExtended_EMLNeuralNetworks

/-! # CatalogBuild.EML.EMLNeuralNetworks

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 27
-/

noncomputable section

theorem emlNeuron_hasDerivAt(w₁ b₁ w₂ b₂ x : ℝ) (h : w₂ * x + b₂ ≠ 0) :
    HasDerivAt (fun x' => emlNeuron w₁ b₁ w₂ b₂ x')
      (w₁ * Real.exp (w₁ * x + b₁) - w₂ / (w₂ * x + b₂)) x := by sorry

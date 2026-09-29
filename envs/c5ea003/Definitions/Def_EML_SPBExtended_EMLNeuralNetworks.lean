-- Prove2me | Definitions.Def_EML_SPBExtended_EMLNeuralNetworks
-- name    : EML_SPBExtended_EMLNeuralNetworks
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:48.974773+00:00
-- url     : https://prove2.me/theorems/d823d666-7b51-45ad-855f-19353f6d35ba
-- title:
--   Aether Catalog definitions — EML_SPBExtended_EMLNeuralNetworks
-- statement:
--   Definition bundle for the Aether Catalog module `EML.SPBExtended.EMLNeuralNetworks`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/SPBExtended/EMLNeuralNetworks.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.EMLNeuralNetworks

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 27
-/

noncomputable section

/-- An EML neuron with parameters (w₁, b₁, w₂, b₂).
Computes f(x) = exp(w₁ · x + b₁) − ln(w₂ · x + b₂). -/
def emlNeuron (w₁ b₁ w₂ b₂ x : ℝ) : ℝ :=
  Real.exp (w₁ * x + b₁) - Real.log (w₂ * x + b₂)







/-- An EML layer: a list of EML neurons applied to the same input. -/
def emlLayer (params : List (ℝ × ℝ × ℝ × ℝ)) (x : ℝ) : List ℝ :=
  params.map fun ⟨w₁, b₁, w₂, b₂⟩ => emlNeuron w₁ b₁ w₂ b₂ x



/-- The parameter count of a dense EML layer with n neurons and m inputs. -/
def emlDenseLayerParams (n m : ℕ) : ℕ := n * (2 * m + 2)










/-- Sigmoid function: σ(x) = 1/(1 + exp(-x)). -/
def emlSigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))




/-- A standard feedforward NN with L layers, width W, needs O(L·W²) parameters. -/
def stdNNTotalParams (L W : ℕ) : ℕ := L * W * (W + 1)

/-- An EML tree with n leaves has n-1 EML operations and 4(n-1) learnable parameters
(each EML node has 4 parameters in the generalized form). -/
def emlTreeTotalParams (n : ℕ) : ℕ := 4 * (n - 1)


end



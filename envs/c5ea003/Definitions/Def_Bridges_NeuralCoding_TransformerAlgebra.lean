-- Prove2me | Definitions.Def_Bridges_NeuralCoding_TransformerAlgebra
-- name    : Bridges_NeuralCoding_TransformerAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:28.556143+00:00
-- url     : https://prove2.me/theorems/9076a338-809d-4ee6-924f-2f02d56df7b1
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_TransformerAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.TransformerAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/TransformerAlgebra.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.MachineLearning.Neural.TransformerAlgebra

Auto-generated from theorem catalog database.
Domain: MachineLearning/Neural
Declarations: 22
-/


open Matrix

noncomputable section

/-- Softmax function on a real-valued vector indexed by `Fin n`. -/
def softmaxVec (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (x i) / ∑ j : Fin n, Real.exp (x j)










/-- A 2D rotation matrix parameterized by angle θ. -/
def rotationMatrix2D (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -(Real.sin θ); Real.sin θ, Real.cos θ]








/-- RoPE frequency for position `pos` and dimension index `k` with base `b`
and model dimension `d`. The frequency is θ_k = pos / b^(2k/d). -/
def ropeFrequency (pos : ℕ) (k : ℕ) (d : ℕ) (base : ℝ) : ℝ :=
  (pos : ℝ) / base ^ ((2 * k : ℝ) / d)


/-- The RoPE rotation for a given position and dimension pair. -/
def ropeRotation (pos : ℕ) (k : ℕ) (d : ℕ) (base : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotationMatrix2D (ropeFrequency pos k d base)




/-- Scaled dot-product scores: S = Q · K^T / √d. -/
def attentionScores (N d : ℕ) (Q K : Matrix (Fin N) (Fin d) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (1 / Real.sqrt d) • (Q * Kᵀ)


/-- Row-wise softmax applied to a matrix. -/
def rowSoftmax (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => softmaxVec N (fun k => M i k) j)








/-- A deterministic layer is a function ℝ^n → ℝ^m with no stochastic component. -/
structure DeterministicLayer (n m : ℕ) where
  forward : (Fin n → ℝ) → (Fin m → ℝ)


/-- Composition of deterministic layers is deterministic. -/
def DeterministicLayer.compose {a b c : ℕ}
    (f : DeterministicLayer b c) (g : DeterministicLayer a b) :
    DeterministicLayer a c where
  forward := f.forward ∘ g.forward








end



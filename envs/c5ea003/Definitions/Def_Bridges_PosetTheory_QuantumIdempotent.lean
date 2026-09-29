-- Prove2me | Definitions.Def_Bridges_PosetTheory_QuantumIdempotent
-- name    : Bridges_PosetTheory_QuantumIdempotent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:21.725979+00:00
-- url     : https://prove2.me/theorems/9eacbd38-a7b4-41c0-a0fe-3999706497eb
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_QuantumIdempotent
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.QuantumIdempotent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/QuantumIdempotent.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.QuantumIdempotent

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 17
-/

noncomputable section

/-- A density matrix is positive semi-definite with trace 1. -/
structure DensityMatrix (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℝ
  symmetric : mat.IsSymm
  trace_one : Matrix.trace mat = 1
  psd : ∀ v : Fin n → ℝ, v ⬝ᵥ (mat.mulVec v) ≥ 0

/-- A pure state density matrix is idempotent: ρ² = ρ. -/
structure PureState (n : ℕ) extends DensityMatrix n where
  idempotent : mat * mat = mat



/-- The purity of a density matrix is tr(ρ²). -/
def purity {n : ℕ} (rho : DensityMatrix n) : ℝ :=
  Matrix.trace (rho.mat * rho.mat)


/-- A spectral decomposition of a density matrix: ρ = Σ pᵢ|ψᵢ⟩⟨ψᵢ|. -/
structure SpectralDecomposition (n : ℕ) where
  num_terms : ℕ
  eigenvalues : Fin num_terms → ℝ
  projectors : Fin num_terms → Matrix (Fin n) (Fin n) ℝ
  eigenvalues_nonneg : ∀ i, eigenvalues i ≥ 0
  eigenvalues_sum_one : ∑ i, eigenvalues i = 1
  projectors_idempotent : ∀ i, projectors i * projectors i = projectors i
  projectors_orthogonal : ∀ i j, i ≠ j → projectors i * projectors j = 0

/-- The density matrix from its spectral decomposition. -/
def SpectralDecomposition.toDensityMat {n : ℕ} (S : SpectralDecomposition n) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, S.eigenvalues i • S.projectors i



/-- The von Neumann entropy S(ρ) = -Σ pᵢ log(pᵢ). -/
def vonNeumannEntropy (k : ℕ) (eigenvalues : Fin k → ℝ) : ℝ :=
  -∑ i, if eigenvalues i > 0
    then eigenvalues i * Real.log (eigenvalues i)
    else 0


/-- The Marchenko-Pastur distribution support bounds. -/
def marchenkoPasturSupport (gamma : ℝ) : ℝ × ℝ :=
  ((1 - Real.sqrt gamma) ^ 2, (1 + Real.sqrt gamma) ^ 2)


/-- A quantum channel as a trace-preserving map. -/
structure QuantumChannel (n : ℕ) where
  channel_map : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
  trace_preserving : ∀ rho, Matrix.trace (channel_map rho) = Matrix.trace rho

/-- A unital quantum channel preserves the identity. -/
structure UnitalChannel (n : ℕ) extends QuantumChannel n where
  unital : channel_map 1 = 1


end



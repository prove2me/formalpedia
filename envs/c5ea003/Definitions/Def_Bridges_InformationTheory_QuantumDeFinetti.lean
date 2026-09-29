-- Prove2me | Definitions.Def_Bridges_InformationTheory_QuantumDeFinetti
-- name    : Bridges_InformationTheory_QuantumDeFinetti
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:05.882216+00:00
-- url     : https://prove2.me/theorems/c2f82815-75f6-4253-b8fe-89473aaaee43
-- title:
--   Aether Catalog definitions — Bridges_InformationTheory_QuantumDeFinetti
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InformationTheory.QuantumDeFinetti`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InformationTheory/QuantumDeFinetti.lean by skeleton subtraction
import Mathlib
/-
  QuantumDeFinetti.lean

  Quantum de Finetti Theorem: Formalization of the bridge between
  quantum exchangeability and classical probability.

  The quantum de Finetti theorem states that symmetric quantum states
  on infinite tensor products are mixtures of i.i.d. states, connecting
  quantum information theory to classical probability via exchangeability.

  Main results:
  1. Symmetric subspace dimension = C(d+k-1, k) with key identities
  2. Finite de Finetti bound properties (monotonicity, linearity)
  3. Purity invariance under unitary conjugation
  4. Classical-quantum bridge: embedding and measurement roundtrip
  5. Herfindahl index = quantum purity for classical states
  6. Purity bounds via Cauchy-Schwarz (1/d ≤ ∑pᵢ² ≤ 1)
  7. Trace preservation for convex combinations of density matrices
-/

open Matrix BigOperators Finset Complex

noncomputable section

namespace QuantumDeFinetti

/-! ## Part I: Definitions -/

/-- Positive semidefiniteness for complex matrices:
    Hermitian with nonneg quadratic form. -/
def IsPosSemidefC {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  M.IsHermitian ∧
  ∀ v : Fin d → ℂ, 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (v i) * M i j * v j).re

/-- A density matrix: pos-semidef complex matrix with trace 1. -/
structure IsDensityMatrix {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop where
  posSemidef : IsPosSemidefC ρ
  traceOne : Matrix.trace ρ = 1

/-- Convex combination of matrices with real weights. -/
def convexComb {d m : ℕ} (w : Fin m → ℝ) (ρs : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, ((w i : ℂ)) • ρs i

/-- Weights form a probability distribution. -/
structure IsProbDist {m : ℕ} (w : Fin m → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  sum_one : ∑ i, w i = 1

/-- Dimension of Sym^k(ℂ^d) = C(d+k-1, k). -/
def symDim (d k : ℕ) : ℕ := (d + k - 1).choose k

/-- Finite quantum de Finetti bound: 2kd²/n. -/
def deFinettiBound (d k n : ℕ) : ℚ := (2 * k * d ^ 2 : ℚ) / n

/-- Purity: Tr(ρ²). -/
def purity {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℂ := Matrix.trace (ρ * ρ)

/-- Linear entropy: S_L(ρ) = 1 - Tr(ρ²). -/
def linearEntropy {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℂ := 1 - purity ρ

/-- Classical embedding: probability distribution → diagonal density matrix. -/
def classicalEmbed {d : ℕ} (p : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => (p i : ℂ))

/-- Measurement: extract diagonal of density matrix. -/
def measureBasis {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Fin d → ℝ :=
  fun i => (ρ i i).re

/-- Conjectured tighter de Finetti bound: kd(d-1)/n. -/
def deFinettiConjectureBound (d k n : ℕ) : ℚ := (k * d * (d - 1) : ℚ) / n

/-! ## Part II: Symmetric Subspace Theorems -/







/-! ## Part III: de Finetti Bound Properties -/




/-
The de Finetti bound decreases monotonically as n → ∞.
-/


/-
The conjectured bound kd(d-1)/n ≤ standard bound 2kd²/n.
-/

/-! ## Part IV: Purity and Unitary Invariance -/





/-! ## Part V: Classical-Quantum Bridge -/


/-
Classical distributions embed as valid density matrices.
-/





/-! ## Part VI: Classical Purity Bounds -/

/-
**Purity upper bound**: ∑ pᵢ² ≤ 1 for probability distributions.
    Equality iff the distribution is a point mass.
-/

/-
**Purity lower bound** (Cauchy-Schwarz): ∑ pᵢ² ≥ 1/d.
    Equality iff the distribution is uniform (maximally mixed state).
-/

/-! ## Part VII: Trace Preservation -/



end QuantumDeFinetti

end



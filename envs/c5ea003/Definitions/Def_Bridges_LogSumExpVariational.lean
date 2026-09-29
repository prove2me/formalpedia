-- Prove2me | Definitions.Def_Bridges_LogSumExpVariational
-- name    : Bridges_LogSumExpVariational
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:46.743054+00:00
-- url     : https://prove2.me/theorems/0e9582d4-898c-48ac-809a-fb5228316078
-- title:
--   Aether Catalog definitions — Bridges_LogSumExpVariational
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LogSumExpVariational`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LogSumExpVariational.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Log-Sum-Exp Variational Formula (Gibbs Variational Principle)

This file proves the finite-dimensional Gibbs variational principle:

  τ * log (∑ᵢ exp(xᵢ/τ)) = sup { ∑ᵢ pᵢxᵢ + τ * H(p) | p ∈ Δₙ }

where H(p) = -∑ᵢ pᵢ log pᵢ is Shannon entropy and Δₙ is the probability simplex.

The proof proceeds via the KL-divergence route:
1. Show that the free energy objective equals τ log Z minus τ * KL(p ∥ q)
   where q is the softmax/Gibbs distribution.
2. Use log x ≤ x - 1 to establish KL nonnegativity.
3. Conclude the upper bound and attainment at the softmax distribution.

## Main Results

* `partitionFun_pos` — positivity of partition function
* `softmaxProb_isProbVec` — softmax defines a probability vector
* `freeEnergy_le_lse` — upper bound: free energy ≤ τ log Z
* `freeEnergy_eq_lse_at_softmax` — attainment at softmax
* `lse_variational_formula` — the exact supremum identity

## Cross-Domain Significance

This theorem connects:
- **Convex analysis**: log-sum-exp as convex conjugate of negative entropy
- **Information theory**: KL divergence nonnegativity
- **Statistical mechanics**: free energy variational principle
- **Machine learning**: softmax as entropy-regularized optimizer
- **Tropical geometry**: dequantization bridge (τ → 0⁺ limit gives max)
-/


open Finset BigOperators Real

/-! ## Section 1: Definitions -/

/-- A probability vector: nonneg entries summing to 1. -/
def IsProbVec {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

/-- Shannon entropy term: -∑ᵢ pᵢ log pᵢ with 0 log 0 = 0 convention. -/
noncomputable def shannonEntropyTerm {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  -∑ i, if p i = 0 then 0 else p i * Real.log (p i)

/-- Free energy objective: ∑ᵢ pᵢxᵢ + τ * H(p). -/
noncomputable def freeEnergyObj {n : ℕ} (τ : ℝ) (x p : Fin n → ℝ) : ℝ :=
  ∑ i, p i * x i + τ * shannonEntropyTerm p

/-- Partition function: Z = ∑ᵢ exp(xᵢ/τ). -/
noncomputable def partitionFun {n : ℕ} (τ : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, Real.exp (x i / τ)

/-- Softmax / Gibbs probability: qᵢ = exp(xᵢ/τ) / Z. -/
noncomputable def softmaxProb {n : ℕ} (τ : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (x i / τ) / partitionFun τ x

/-! ## Section 2: Basic Properties of Partition Function and Softmax -/






/-
Log of softmax probability: log(qᵢ) = xᵢ/τ - log Z.
-/

/-! ## Section 3: KL Divergence and Gibbs Inequality -/

/-
Scalar KL inequality: for u ≥ 0 and v > 0, u * log(u/v) ≥ u - v.
    This is the key analytic inequality underlying KL nonnegativity.
-/

/-
Finite Gibbs inequality (KL divergence nonnegativity):
    For probability vectors p and strictly positive q,
    ∑ᵢ pᵢ log(pᵢ/qᵢ) ≥ 0 (with 0 log 0 = 0 convention).
-/

/-! ## Section 4: Free Energy Upper Bound -/

/-
The free energy of any probability vector is at most τ * log Z.
    This is the upper bound half of the variational principle.
-/

/-! ## Section 5: Attainment at Softmax -/

/-
The free energy objective evaluated at the softmax distribution
    equals τ * log Z exactly.
-/


/-! ## Section 6: Supremum Formulation -/

/-
**Gibbs Variational Principle / Log-Sum-Exp Duality**:

    τ * log(∑ᵢ exp(xᵢ/τ)) = sup { ∑ᵢ pᵢxᵢ + τ H(p) | p is a probability vector }

    This is the finite-dimensional Legendre–Fenchel duality between log-sum-exp
    and negative Shannon entropy on the probability simplex.
-/



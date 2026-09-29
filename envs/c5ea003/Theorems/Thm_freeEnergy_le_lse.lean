-- Prove2me | Theorems.Thm_freeEnergy_le_lse
-- name    : freeEnergy_le_lse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:32:37.166425+00:00
-- url     : https://prove2.me/theorems/1a7eae46-42fd-48db-94bc-519d09bf6247
-- title:
--   FreeEnergy le lse
-- statement:
--   Formal statement of `freeEnergy_le_lse` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem freeEnergy_le_lse{n : ℕ} (hn : 0 < n) (τ : ℝ) (hτ : 0 < τ) (x p : Fin n → ℝ)
--       (hp : IsProbVec p) :
--       freeEnergyObj τ x p ≤ τ * Real.log (partitionFun τ x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/LogSumExpVariational.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/LogSumExpVariational.lean#L125

-- Thm stub generated from Bridges/LogSumExpVariational.lean
import Mathlib
import Definitions.Def_Bridges_LogSumExpVariational
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

theorem freeEnergy_le_lse{n : ℕ} (hn : 0 < n) (τ : ℝ) (hτ : 0 < τ) (x p : Fin n → ℝ)
    (hp : IsProbVec p) :
    freeEnergyObj τ x p ≤ τ * Real.log (partitionFun τ x) := by sorry

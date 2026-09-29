-- Prove2me | Definitions.Def_Bridges_ThermodynamicArithmeticOrbits
-- name    : Bridges_ThermodynamicArithmeticOrbits
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:38.825415+00:00
-- url     : https://prove2.me/theorems/3c18f2c8-80c2-4214-8a54-41aa9eca60e9
-- title:
--   Aether Catalog definitions — Bridges_ThermodynamicArithmeticOrbits
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ThermodynamicArithmeticOrbits`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ThermodynamicArithmeticOrbits.lean by skeleton subtraction
import Mathlib
/-
# Thermodynamic Formalism for Arithmetic Orbits

This file establishes a rigorous bridge between discounted arithmetic-orbit
value functions and thermodynamic partition-function formalism. The central
result is an exact decomposition of the "free energy" of an arithmetic
system as a generating function of stopping-time tail masses, together
with comparison theorems that relate the divergence rate of this free
energy as γ → 1⁻ to tail-exponent statistics of the stopping time.

## Main results

* `discounted_cost_eq_geometric_sum` — geometric-sum identity for discounted orbit cost
* `freeEnergyTrunc_eq_tail_sum` — exact decomposition of truncated free energy
* `freeEnergyTrunc_nonneg` — positivity under nonneg weights
* `tailMassTrunc_antitone` — tail masses are nonincreasing
* `freeEnergyTrunc_upper_bound_of_tail_upper` — upper comparison from tail bounds
* `freeEnergyTrunc_lower_bound_of_tail_lower` — lower comparison from tail bounds
* `freeEnergyTrunc_sandwich` — two-sided sandwich theorem
-/


open Finset BigOperators

noncomputable section

-- The discounted cost of orbit n: sum of γᵏ for k < τ(n).
def discountedCost (τ : ℕ → ℕ) (γ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (τ n), γ ^ k

-- Truncated free energy: weighted sum of discounted costs over {1, ..., N}.
def freeEnergyTrunc (τ : ℕ → ℕ) (w : ℕ → ℝ) (N : ℕ) (γ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, w n * discountedCost τ γ n

-- Tail mass at level m: total weight of n ∈ {1,...,N} with τ(n) > m.
def tailMassTrunc (τ : ℕ → ℕ) (w : ℕ → ℝ) (N : ℕ) (m : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < τ n), w n

-- The reference partition function: Σ_{m<M} γᵐ (m+1)⁻ᵝ.
def polylogPartition (γ β : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, γ ^ m / (↑m + 1) ^ β

/-
════════════════════════════════════════════════════════════════════════
§ Geometric sum identity
════════════════════════════════════════════════════════════════════════

The discounted cost equals the closed-form geometric sum (1 - γ^τ)/(1 - γ).
-/

/-
════════════════════════════════════════════════════════════════════════
§ Exact decomposition: free energy = generating function of tails
════════════════════════════════════════════════════════════════════════

**Main decomposition theorem** (bounded-support variant).
When all stopping times satisfy τ(n) ≤ M for n ∈ {1,...,N}, the free energy
decomposes exactly as Σ_{m<M} γᵐ · tailMassTrunc(m).
-/

/-
════════════════════════════════════════════════════════════════════════
§ Positivity and monotonicity
════════════════════════════════════════════════════════════════════════

Free energy is nonneg when weights and γ are nonneg.
-/

/-
Tail masses are nonneg when weights are nonneg.
-/

/-
Tail masses are nonincreasing: if m₁ ≤ m₂ then tail(m₂) ≤ tail(m₁).
-/

/-
════════════════════════════════════════════════════════════════════════
§ Comparison bounds
════════════════════════════════════════════════════════════════════════

**Upper comparison**: if tail masses are bounded above by B·(m+1)⁻ᵝ,
then the free energy is bounded above by B times the polylog partition function.
-/

/-
**Lower comparison**: if tail masses are bounded below by A·(m+1)⁻ᵝ for m < M,
then the free energy is bounded below by A times the polylog partition function.
-/

/-
════════════════════════════════════════════════════════════════════════
§ Sandwich theorem
════════════════════════════════════════════════════════════════════════

**Sandwich theorem**: two-sided power-law tail bounds yield two-sided
free-energy bounds. This identifies the critical exponent of free-energy
divergence with the tail exponent of stopping times.
-/

-- ════════════════════════════════════════════════════════════════════════
-- § Collatz specialization interface
-- ════════════════════════════════════════════════════════════════════════





end



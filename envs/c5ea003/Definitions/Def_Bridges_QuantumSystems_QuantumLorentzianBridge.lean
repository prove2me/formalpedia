-- Prove2me | Definitions.Def_Bridges_QuantumSystems_QuantumLorentzianBridge
-- name    : Bridges_QuantumSystems_QuantumLorentzianBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:08.34621+00:00
-- url     : https://prove2.me/theorems/cbc26153-86f1-4ca2-9668-ecd0b7be7a31
-- title:
--   Aether Catalog definitions — Bridges_QuantumSystems_QuantumLorentzianBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantumSystems.QuantumLorentzianBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantumSystems/QuantumLorentzianBridge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Robust Log-Concavity for Quantum Many-Body Ground States

This file formalizes a **bridge between quantum many-body spectral theory,
Lorentzian/strongly log-concave polynomials, and classical Markov-chain expansion**.

## Mathematical Vision

Given a normalized quantum state `ψ : α → ℂ`, its computational-basis measurement
distribution `μ(x) = ‖ψ(x)‖²` defines a probability measure on the configuration
space. For free-fermionic and determinantal states, the generating polynomial of `μ`
is Lorentzian / strongly log-concave. We formalize:

1. **Perturbative transport** — pointwise multiplicative closeness of distributions
   transfers to event-level probability control.
2. **Gap surrogate preservation** — minimum mass and anti-concentration certificates
   degrade gracefully under multiplicative perturbation.
3. **Cross-domain bridge** — boundary mass (graph expansion) of a spin system is
   controlled by perturbative comparison to a reference distribution.

## Application Keywords

quantum many-body systems, transverse-field Ising model, free fermions,
matchgate circuits, Lorentzian polynomials, strong log-concavity, spectral gap,
Glauber dynamics, anti-concentration, negative dependence, perturbation stability,
classical simulation, combinatorial Hodge theory, determinantal processes,
quantum-to-classical correspondence

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Anari–Liu–Oveis Gharan–Vinzant, "Log-Concave Polynomials II", Annals of Mathematics, 2021
* Builds on `Catalog.Bridges.Catalog.Pythagorean.RobustLorentzianSampling.gibbs_pointwise_ratio_bound`
-/

open Finset BigOperators

noncomputable section

namespace QuantumLorentzianBridge

/-! ## Core Definitions -/

/-- A quantum measurement model: a normalized pure state in the computational basis.
    The amplitudes `amp` satisfy `∑ x, ‖amp x‖² = 1`. -/
structure QuantumMeasurementModel (α : Type*) [Fintype α] where
  amp : α → ℂ
  norm_one : ∑ x, ‖amp x‖ ^ 2 = 1

/-- The induced probability mass function of a quantum measurement model. -/
def QuantumMeasurementModel.prob
    {α : Type*} [Fintype α] (M : QuantumMeasurementModel α) : α → ℝ :=
  fun x => ‖M.amp x‖ ^ 2


/-- A gapped measurement lift: an abstract object connecting quantum spectral gaps,
    Lorentzian gaps, and classical expansion gaps. -/
structure GappedMeasurementLift (α : Type*) [Fintype α] where
  μ : α → ℝ
  quantumGap : ℝ
  lorentzianGap : ℝ
  classicalGap : ℝ
  quantumGap_nonneg : 0 ≤ quantumGap
  lorentzianGap_nonneg : 0 ≤ lorentzianGap
  classicalGap_nonneg : 0 ≤ classicalGap
  q_to_l : quantumGap ≤ lorentzianGap
  l_to_c : lorentzianGap ≤ classicalGap

/-- A finite spin system: a probability distribution on a finite type
    equipped with a decidable symmetric edge relation. -/
structure FiniteSpinSystem (α : Type*) [Fintype α] [DecidableEq α] where
  μ : α → ℝ
  adj : α → α → Bool
  adj_symm : ∀ x y, adj x y = adj y x
  μ_nonneg : ∀ x, 0 ≤ μ x
  μ_sum_one : ∑ x, μ x = 1

/-- Whether a vertex `x` in `A` has a neighbor outside `A`. -/
def hasBoundaryNeighbor
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : FiniteSpinSystem α) (A : Finset α) (x : α) : Bool :=
  (Finset.univ.filter fun y => S.adj x y = true ∧ y ∉ A).card > 0

/-- The boundary mass of a set `A` in a finite spin system: the total mass of
    elements in `A` that have at least one neighbor outside `A`. -/
def boundaryMass
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : FiniteSpinSystem α) (A : Finset α) : ℝ :=
  ∑ x ∈ A, if hasBoundaryNeighbor S A x then S.μ x else 0

/-- Minimum mass of a distribution: the smallest probability assigned to any element. -/
def minMass {α : Type*} [Fintype α] [Nonempty α] (μ : α → ℝ) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty μ

/-! ## Theorem 0: Basic Properties of Quantum Measurement Models -/


/-
The measurement probabilities sum to 1.
-/

/-! ## Theorem 1: Perturbative Transfer of Pointwise Control to Event Probabilities

This theorem is the perturbative engine: if `μ` is pointwise multiplicatively
close to `ν` (with factor `exp(ε)`), then for any event `s ⊆ α`, the total
probability of `s` under `μ` is within a factor of `exp(ε)` of its probability
under `ν`.

**Why it matters:** This upgrades pointwise ratio control (from catalog's
`gibbs_pointwise_ratio_bound`) into observable control for measurement events,
the minimum interface needed to connect quantum observables to classical
Lorentzian sampling statements.
-/


/-! ## Theorem 2: Minimum Mass Perturbation Lower Bound

The minimum mass (anti-concentration certificate) degrades by at most
a multiplicative factor of `exp(-ε)` under `exp(ε)`-multiplicative perturbation.

**Why it matters:** This gives a rigorous perturbative notion of a Lorentzian
gap surrogate, suitable for current Mathlib and extensible to actual
Hessian-based Lorentzian gap definitions.
-/


/-! ## Theorem 3: Boundary Mass Monotonicity Under Pointwise Lower Bound

If the distribution `S.μ` pointwise dominates `T.μ`, then the boundary
mass of `S` dominates that of `T` for any subset `A`.
-/


/-! ## Theorem 4: Cross-Domain Bridge — Perturbative Boundary Mass Lower Bound

This is the central cross-domain theorem. It connects:
- **quantum side:** `S.μ` is a measurement law of a ground state
- **classical side:** `boundaryMass` is a graph-expansion quantity for Glauber/local moves
- **geometric side:** the reference `T.μ` can come from a Lorentzian/determinantal model

The theorem says that if two spin systems share the same edge structure and their
distributions are multiplicatively close, then the boundary mass (expansion) of one
is at least `exp(-ε)` times that of the other.

**Why it matters:** This is a legitimate first formal bridge between quantum
measurement distributions and classical graph-expansion / Markov-chain analysis.
-/


/-! ## Theorem 5: Quantum-to-Classical Gap Bridge

The full gap bridge: quantum gap ≤ Lorentzian gap ≤ classical gap, and the
quantum gap controls event anti-concentration.
-/


/-! ## Conjectural Shell: Robust Lorentzian Gap from Quantum Gap

This states a falsifiable quantitative conjecture: the quantum gap of a
Hamiltonian, divided by a polynomial in the system size, lower-bounds
both the Lorentzian gap and the classical expansion gap.
-/


end QuantumLorentzianBridge



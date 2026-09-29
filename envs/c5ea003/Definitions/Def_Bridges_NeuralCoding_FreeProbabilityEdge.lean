-- Prove2me | Definitions.Def_Bridges_NeuralCoding_FreeProbabilityEdge
-- name    : Bridges_NeuralCoding_FreeProbabilityEdge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:15.380318+00:00
-- url     : https://prove2.me/theorems/3b09165e-8882-45cd-a8e0-33eb37653e20
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_FreeProbabilityEdge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.FreeProbabilityEdge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/FreeProbabilityEdge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Free Probability Edge Functional and Structured Noise Certification

This file formalizes a **structured-noise spectral edge functional** arising from
free additive convolution of a deterministic spectrum with semicircular noise.
It replaces the universal `2σ` GOE threshold with a structurally informed
certification boundary governed by the **free spectral edge**.

## Mathematical Context

For a deterministic self-adjoint spectrum μ (encoded as a finite atomic probability
measure) and semicircular noise of variance σ², the rightmost support point of the
free additive convolution μ ⊞ SC_σ is characterized by a fixed-point equation
involving the Stieltjes-transform denominator:

  f_μ(x) = Σᵢ wᵢ / (x − aᵢ)² = 1 / σ²

on the domain x > max_i aᵢ. This equation has at most one solution (by strict
monotonicity of f_μ), and that unique solution is the **free spectral edge** R(μ,σ).

## Main Definitions

* `SpectralAtom` — weighted point mass in a finite spectrum
* `FiniteSpectrumLaw` — finite atomic probability law on ℝ
* `FiniteSpectrumLaw.stieltjesDenom` — the Cauchy-transform denominator Σ wᵢ/(x−aᵢ)²
* `FreeSemicircleEdgeCandidate` — the free-edge equation f_μ(x) = 1/σ²
* `freeRightEdge` — the set of free-edge candidates
* `spikeLaw` — the rank-one deformation spike law μ_{n,λ}
* `QuantumSpectralMargin` — cross-domain bridge to Hamiltonian stability

## Main Results

* `finiteSpectrum_stieltjesDenom_nonneg` — positivity of the Stieltjes denominator
* `finiteSpectrum_stieltjesDenom_strictAnti` — strict monotonicity
* `free_edge_candidate_unique` — uniqueness of the free-edge equation solution
* `free_edge_gap_positive` — the free edge exceeds all spectral atoms
* `spikeLaw_edge_equation` — explicit algebraic edge equation for the spike model
* `zeroLaw_edge_reduces_to_classical` — recovery of σ in the trivial-spectrum case
* `free_edge_monotone_in_noise` — monotonicity of the free edge in noise strength
* `quantumSpectralMargin_above_energy_levels` — Hamiltonian stability bridge

## Application Keywords

free probability, free convolution, semicircle law, random matrix theory,
spectral edge, structured noise, smoothed analysis, certified robustness,
operator algebras, quantum information, spiked models, BBP transition,
Hamiltonian stability, noncommutative probability, spectral algorithms

## References

* Voiculescu, "Addition of certain noncommuting random variables", JFA, 1986
* Baik–Ben Arous–Péché, "Phase transition of the largest eigenvalue", Ann. Prob., 2005
* Biane, "Processes with free increments", Math. Z., 1998
-/

open Finset BigOperators Real

noncomputable section

namespace FreeProbabilityEdge

/-! ## Core Definitions -/

/-- A spectral atom: a weighted point mass in a finite spectrum. -/
structure SpectralAtom where
  /-- Location of the atom -/
  loc : ℝ
  /-- Weight (probability mass) -/
  weight : ℝ
  /-- Weights are nonneg -/
  weight_nonneg : 0 ≤ weight

/-- A finite atomic probability law on ℝ. -/
structure FiniteSpectrumLaw where
  /-- The atoms of the law -/
  atoms : List SpectralAtom
  /-- The atoms are nonempty -/
  atoms_nonempty : atoms ≠ []
  /-- Total mass is 1 -/
  mass_one : (atoms.map (·.weight)).sum = 1

/-- The Stieltjes-transform denominator, encoding the second-moment functional
    f_μ(x) = Σᵢ wᵢ / (x − aᵢ)². This is the key quantity whose equation
    f_μ(x) = 1/σ² characterizes the free spectral edge. -/
def FiniteSpectrumLaw.stieltjesDenom (μ : FiniteSpectrumLaw) (x : ℝ) : ℝ :=
  (μ.atoms.map (fun a => a.weight / (x - a.loc) ^ 2)).sum

/-- The free semicircle edge candidate: x satisfies the free-edge equation
    if it lies to the right of all atoms and solves f_μ(x) = 1/σ². -/
def FreeSemicircleEdgeCandidate (μ : FiniteSpectrumLaw) (σ x : ℝ) : Prop :=
  (∀ a ∈ μ.atoms, a.loc < x) ∧ μ.stieltjesDenom x = 1 / σ ^ 2

/-- The set of all free-edge candidates. -/
def freeRightEdge (μ : FiniteSpectrumLaw) (σ : ℝ) : Set ℝ :=
  {x | FreeSemicircleEdgeCandidate μ σ x}


/-! ## Spike Law -/

/-- The spike law: one atom at `spike` with weight 1/n, one at 0 with weight (n-1)/n.
    This models a rank-one perturbation of the zero matrix. -/
def spikeLaw (n : ℕ) (hn : 0 < n) (spike : ℝ) : FiniteSpectrumLaw where
  atoms := [
    ⟨spike, 1 / (n : ℝ), by positivity⟩,
    ⟨0, ((n : ℝ) - 1) / (n : ℝ), by
      apply div_nonneg _ (by positivity)
      linarith [show (1 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hn]⟩
  ]
  atoms_nonempty := List.cons_ne_nil _ _
  mass_one := by
    simp [List.map, List.sum_cons]
    field_simp
    linarith [show (0 : ℝ) < (n : ℝ) from by exact_mod_cast hn]

/-! ## Quantum Spectral Margin (Cross-Domain Bridge) -/

/-- The quantum spectral margin: the same free edge, interpreted as a threshold
    for stability of a finite-dimensional Hamiltonian under semicircular-type noise. -/
def QuantumSpectralMargin (μ : FiniteSpectrumLaw) (σ : ℝ) : Set ℝ :=
  freeRightEdge μ σ

/-! ## Helper Lemmas -/




/-! ## Main Theorems -/

/-
**Theorem 1 (Strict Monotonicity).** The Stieltjes denominator f_μ is strictly
    decreasing on x > max support, provided there exists at least one atom with
    positive weight.
-/

/-
**Theorem 2 (Uniqueness).** The free-edge equation f_μ(x) = 1/σ² has at most
    one solution on x > max support.
-/



/-
**Theorem 5 (Classical Recovery).** For the spike law with n=1 and spike=0,
    the free-edge equation reduces to x = σ.
-/

/-
**Theorem 6 (Spike Law Edge Equation).** For the spike law μ_{n,spike},
    the free-edge equation becomes an explicit algebraic relation.
-/

/-
**Theorem 7 (Monotonicity in Noise).**
    If σ ≤ τ (more noise), the free edge moves further right.
-/


/-! ## Verified Computational Method -/

/-- Bisection approximation of the free right edge. -/
def approximateFreeRightEdge
    (μ : FiniteSpectrumLaw) (sigma left right : ℝ) : ℕ → ℝ
  | 0 => (left + right) / 2
  | n + 1 =>
    let mid := (left + right) / 2
    let target := 1 / sigma ^ 2
    if μ.stieltjesDenom mid > target then
      approximateFreeRightEdge μ sigma mid right n
    else
      approximateFreeRightEdge μ sigma left mid n

/-
The bisection output lies between the initial endpoints.
-/

end FreeProbabilityEdge



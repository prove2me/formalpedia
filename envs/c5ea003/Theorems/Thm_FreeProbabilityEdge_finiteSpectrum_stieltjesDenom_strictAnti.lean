-- Prove2me | Theorems.Thm_FreeProbabilityEdge_finiteSpectrum_stieltjesDenom_strictAnti
-- name    : FreeProbabilityEdge.finiteSpectrum_stieltjesDenom_strictAnti
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:05.906291+00:00
-- url     : https://prove2.me/theorems/8bba7135-9527-4b17-bf33-52fcbd41127d
-- title:
--   FiniteSpectrum stieltjesDenom strictAnti
-- statement:
--   Formal statement of `FreeProbabilityEdge.finiteSpectrum_stieltjesDenom_strictAnti` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FreeProbabilityEdge.finiteSpectrum_stieltjesDenom_strictAnti    (μ : FiniteSpectrumLaw) {x y : ℝ}
--       (hpos : ∃ a ∈ μ.atoms, 0 < a.weight)
--       (hx : ∀ a ∈ μ.atoms, a.loc < x)
--       (hy : ∀ a ∈ μ.atoms, a.loc < y)
--       (hxy : x < y) :
--       μ.stieltjesDenom y < μ.stieltjesDenom x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/FreeProbabilityEdge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/FreeProbabilityEdge.lean#L165

-- Thm stub generated from Bridges/NeuralCoding/FreeProbabilityEdge.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_FreeProbabilityEdge
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

open FreeProbabilityEdge

/-! ## Core Definitions -/







/-! ## Spike Law -/


/-! ## Quantum Spectral Margin (Cross-Domain Bridge) -/


/-! ## Helper Lemmas -/




/-! ## Main Theorems -/

/-
**Theorem 1 (Strict Monotonicity).** The Stieltjes denominator f_μ is strictly
    decreasing on x > max support, provided there exists at least one atom with
    positive weight.
-/

theorem FreeProbabilityEdge.finiteSpectrum_stieltjesDenom_strictAnti    (μ : FiniteSpectrumLaw) {x y : ℝ}
    (hpos : ∃ a ∈ μ.atoms, 0 < a.weight)
    (hx : ∀ a ∈ μ.atoms, a.loc < x)
    (hy : ∀ a ∈ μ.atoms, a.loc < y)
    (hxy : x < y) :
    μ.stieltjesDenom y < μ.stieltjesDenom x := by sorry

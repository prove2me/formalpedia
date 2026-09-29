-- Prove2me | solution 1 for FreeProbabilityEdge.finiteSpectrum_stieltjesDenom_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:41:18.221255+00:00
-- url     : https://prove2.me/submissions/a4f51c2f-fd66-4593-94cc-2e4b7c043133

-- Sol generated from Bridges/NeuralCoding/FreeProbabilityEdge.lean
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


/-
The bisection output lies between the initial endpoints.
-/


open FreeProbabilityEdge in
theorem solution    (μ : FiniteSpectrumLaw) {x y : ℝ}
    (hpos : ∃ a ∈ μ.atoms, 0 < a.weight)
    (hx : ∀ a ∈ μ.atoms, a.loc < x)
    (hy : ∀ a ∈ μ.atoms, a.loc < y)
    (hxy : x < y) :
    μ.stieltjesDenom y < μ.stieltjesDenom x := by
  convert List.sum_lt_sum ?_ ?_ using 1; simp_all +decide [ StrictAntiOn, StrictMonoOn, StrictAntiOn ] ;
  rotate_left;
  any_goals exact μ.atoms;
  exact ℝ;
  all_goals try infer_instance;
  exact fun a => a.weight / ( y - a.loc ) ^ 2;
  exact fun a => a.weight / ( x - a.loc ) ^ 2;
  constructor <;> intro h <;> contrapose! h <;> simp_all +decide [ div_eq_mul_inv ];
  · exact h.2.choose_spec.2.2;
  · refine' ⟨ _, _ ⟩;
    · intro a ha; exact mul_le_mul_of_nonneg_left ( inv_anti₀ ( sq_pos_of_pos ( sub_pos.mpr ( hx a ha ) ) ) ( by nlinarith [ hx a ha, hy a ha ] ) ) ( by linarith [ hx a ha, hy a ha, show 0 ≤ a.weight from a.weight_nonneg ] ) ;
    · exact ⟨ hpos.choose, hpos.choose_spec.1, mul_lt_mul_of_pos_left ( inv_strictAnti₀ ( sq_pos_of_pos ( sub_pos.mpr ( hx _ hpos.choose_spec.1 ) ) ) ( by nlinarith [ hx _ hpos.choose_spec.1, hy _ hpos.choose_spec.1 ] ) ) hpos.choose_spec.2, h ⟩

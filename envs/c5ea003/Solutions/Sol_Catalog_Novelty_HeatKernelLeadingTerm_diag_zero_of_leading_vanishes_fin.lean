-- Prove2me | solution 1 for Catalog.Novelty.HeatKernelLeadingTerm.diag_zero_of_leading_vanishes_fin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:58:59.211692+00:00
-- url     : https://prove2.me/submissions/0dfc1f85-72a4-4177-a151-3a448c4d9506

-- Sol generated from Novelty/HeatKernelLeadingTerm.lean
import Mathlib
import Definitions.Def_Novelty_HeatKernelLeadingTerm
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cancellation of the leading correction in a spectral heat-kernel expansion

Consider a quantum system whose unperturbed Hamiltonian has a discrete spectrum
`E : Fin n → ℝ` and which is deformed by a small perturbation of strength `1/N`.
First-order (Rayleigh–Schrödinger / Feynman–Hellmann) perturbation theory shifts
each energy level by its diagonal matrix element `dᵢ = ⟨i|V|i⟩`, so the leading
`1/N` correction to the heat-kernel trace `Z(t) = Tr e^{-tH}` is the spectral
function

  `L(t) = ∑ᵢ dᵢ · e^{-t Eᵢ}`.

This file characterises **exactly when the leading `1/N` term cancels**, i.e. when
`L(t) = 0` for every inverse temperature `t`.

## Main results

* `heatKernelLeading_trace` — evaluating at `t = 0` recovers the trace of the
  perturbation: `L(0) = ∑ᵢ dᵢ`.
* `trace_zero_of_leading_vanishes` — if the leading term cancels for all `t`,
  then the perturbation is traceless.
* `diag_zero_of_leading_vanishes` — **(non-degenerate spectrum)** if the levels
  `Eᵢ` are distinct and the leading term cancels for all `t`, then *every*
  diagonal matrix element vanishes. The proof turns the analytic vanishing into
  a Vandermonde linear system by sampling `t = 0, 1, 2, …` and using the
  distinctness of `e^{-Eᵢ}`.
* `heatKernelLeading_vanishes_iff` — **(non-degenerate spectrum)** the leading
  term cancels for all `t` **iff** the perturbation is diagonal-free.
* `heatKernelLeading_vanishes_iff_levelSums` — **(general spectrum, allowing
  degeneracy)** the leading term cancels for all `t` **iff** the sum of diagonal
  matrix elements over each degenerate energy level is zero. This is the sharp
  form: cancellation happens level-by-level, not term-by-term.
* `leading_vanishes_of_level_antisymmetric` — a concrete two-level illustration:
  a degenerate doublet with opposite diagonal matrix elements cancels identically.

## Tags
heat kernel, spectral expansion, perturbation theory, leading term cancellation,
Vandermonde, degeneracy, large-N

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).**  In a large-`N` expansion of a heat-kernel trace,
the leading `1/N` correction is the spectral sum `L(t) = ∑ᵢ dᵢ e^{-tEᵢ}` with
`dᵢ` the first-order level shift. We conjectured that this leading term cannot
vanish "by accident": for a non-degenerate spectrum it must vanish term-by-term,
and in general the only mechanism is cancellation *within* each degenerate level.

**Experiment (Experimenter).**  Two-level check with `E = (a,a)` (degenerate) and
`d = (c, -c)`: `L(t) = c e^{-ta} - c e^{-ta} = 0` for all `t` ✓, even though no
individual `dᵢ` vanishes. With distinct levels `E = (0,1)` and `d = (1,-1)`:
`L(t) = 1 - e^{-t}`, which is nonzero for `t > 0` — cancellation fails, matching
the prediction that distinct levels forbid nontrivial cancellation.

**Analysis (Analyst).**  Sampling `L` at natural-number values of `t` converts
the transcendental identity into `∑ᵢ dᵢ xᵢ^k = 0` for all `k`, where
`xᵢ = e^{-Eᵢ}`. Distinct levels give distinct positive `xᵢ`, so the coefficient
vector lies in the kernel of an invertible Vandermonde matrix and must be zero.
Degeneracy is handled by pushing the identity forward to the (distinct) set of
energy values; the fibre sums become the new coefficients.

**Critique (Critic).**  The non-degenerate hypothesis is genuinely needed: the
two-level degenerate example is a nonzero coefficient vector with `L ≡ 0`, so
`diag_zero_of_leading_vanishes` is false without injectivity of `E`. The general
theorem `heatKernelLeading_vanishes_iff_levelSums` is the guarded, sharp version.
No result is vacuous: each direction is exhibited on explicit spectra above.

**Synthesis (PI).**  The leading `1/N` term is a linear combination of the
linearly-independent functions `t ↦ e^{-tEᵢ}` grouped by level; its cancellation
is equivalent to the vanishing of each level's aggregate diagonal shift. This is
a clean bridge between spectral analysis (exponential linear independence),
linear algebra (Vandermonde), and the combinatorics of spectral degeneracy.
-/

open scoped BigOperators
open Matrix

open Catalog.Novelty.HeatKernelLeadingTerm













open Catalog.Novelty.HeatKernelLeadingTerm in
theorem solution{n : ℕ} (E d : Fin n → ℝ)
    (hE : Function.Injective E)
    (h : ∀ t : ℝ, ∑ i, d i * Real.exp (-(t * E i)) = 0) : ∀ i, d i = 0 := by
  classical
  set x : Fin n → ℝ := fun i => Real.exp (-E i) with hx
  have hxinj : Function.Injective x := by
    intro a b hab; apply hE; have := Real.exp_injective hab; linarith
  -- The identity, sampled at natural `t = k`, becomes a vanishing moment.
  have hmom : ∀ k : ℕ, ∑ i, x i ^ k * d i = 0 := by
    intro k
    have hk := h (k : ℝ); rw [← hk]
    apply Finset.sum_congr rfl; intro i _; rw [hx]
    have h2 : Real.exp (-(↑k * E i)) = Real.exp (-E i) ^ k := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]; ring
  -- Assemble the (transposed) Vandermonde matrix and read off `M · d = 0`.
  set M : Matrix (Fin n) (Fin n) ℝ := (Matrix.vandermonde x)ᵀ with hM
  have hMv : M.mulVec d = 0 := by
    funext k
    rw [show M.mulVec d k = ∑ j, M k j * d j by simp [Matrix.mulVec, dotProduct]]
    simp only [hM, Matrix.transpose_apply, Matrix.vandermonde_apply, Pi.zero_apply]
    exact hmom k
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_transpose, Matrix.det_vandermonde]
    apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    have hij : i ≠ j := by simp only [Finset.mem_Ioi] at hj; exact ne_of_lt hj
    exact sub_ne_zero.mpr (fun hxx => hij (hxinj hxx).symm)
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hcon
  have hdne : d ≠ 0 := fun hd0 => hi0 (by rw [hd0]; rfl)
  have hex : ∃ v, v ≠ 0 ∧ M.mulVec v = 0 := ⟨d, hdne, hMv⟩
  rw [Matrix.exists_mulVec_eq_zero_iff] at hex
  exact hdet hex

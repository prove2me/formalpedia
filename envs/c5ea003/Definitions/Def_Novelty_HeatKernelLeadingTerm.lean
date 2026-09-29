-- Prove2me | Definitions.Def_Novelty_HeatKernelLeadingTerm
-- name    : Novelty_HeatKernelLeadingTerm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:24.808881+00:00
-- url     : https://prove2.me/theorems/bd0837fb-5515-4450-ba7e-b04a78756094
-- title:
--   Aether Catalog definitions — Novelty_HeatKernelLeadingTerm
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.HeatKernelLeadingTerm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/HeatKernelLeadingTerm.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Novelty.HeatKernelLeadingTerm

/-- The leading `1/N` correction to the heat-kernel trace: with unperturbed
energy levels `E` and first-order diagonal shifts `d`, this is the spectral
function `L(t) = ∑ᵢ dᵢ e^{-t Eᵢ}`. -/
noncomputable def heatKernelLeading {n : ℕ} (E d : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, d i * Real.exp (-(t * E i))











end Catalog.Novelty.HeatKernelLeadingTerm



-- Prove2me | Definitions.Def_Cryptography_LWE_LatticeProblems
-- name    : Cryptography_LWE_LatticeProblems
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:01.509473+00:00
-- url     : https://prove2.me/theorems/b0f15eff-32e5-43d7-9c31-a05dc4aaddfc
-- title:
--   Aether Catalog definitions — Cryptography_LWE_LatticeProblems
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.LatticeProblems`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/LatticeProblems.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Worst-Case Lattice Problems: Successive Minima, GapSVP, SIVP

This module formalizes the *worst-case* lattice problems that sit on the hard end
of the Regev worst-case-to-average-case reduction for Learning with Errors (LWE):
the decisional **GapSVP** (approximate shortest vector) and the search **SIVP**
(shortest independent vectors).  Both are phrased through the *successive minima*
spectrum `λ₁ ≤ λ₂ ≤ ⋯ ≤ λ_d` of a `d`-dimensional lattice.

Rather than re-develop the full geometry of numbers, we abstract a lattice by its
successive-minima spectrum: a strictly positive, monotone family
`lam : Fin d → ℝ`.  This is faithful — successive minima of an honest lattice are
always positive and nondecreasing — and it isolates exactly the ordering data on
which the elementary lattice-problem relations depend.

## Main results

* `LatticeSpectrum.lambda1_le_lam` / `lam_le_lambdaN` — `λ₁` is the minimum and
  `λ_d` the maximum of the spectrum.
* `LatticeSpectrum.sum_lam_ge` / `sum_lam_le` — the trace of the spectrum is
  sandwiched: `d·λ₁ ≤ Σ λ_i ≤ d·λ_d`.
* `LatticeSpectrum.gapSVP_promise_disjoint` — the YES and NO promises of
  `GapSVP_γ` are genuinely disjoint whenever `γ ≥ 1`.
* `LatticeSpectrum.sivp_factor_ge_one` — any `SIVP_γ` solution forces `γ ≥ 1`.
* `LatticeSpectrum.bdd_uniqueness_gap` — the decoding radius `α·λ₁` with `α < 1/2`
  is strictly below `λ₁`, the uniqueness condition behind Bounded Distance
  Decoding (the average-case target of the reduction).

## References

* Regev, "On Lattices, Learning with Errors, Random Linear Codes, and
  Cryptography", STOC 2005 / JACM 2009.
* Micciancio & Regev, "Worst-Case to Average-Case Reductions Based on Gaussian
  Measures", SIAM J. Comput. 2007.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the elementary content of the lattice problems
GapSVP and SIVP is *entirely order-theoretic* once we fix the successive-minima
spectrum; the geometry only enters when relating the spectrum to Gaussian
measures (handled in `DiscreteGaussian.lean`).

Experiment (Experimenter): encode a lattice as a positive monotone spectrum
`lam : Fin d → ℝ`; derive min/max characterisations of `λ₁, λ_d`; the trace
sandwich; promise-disjointness of `GapSVP_γ`; and the BDD uniqueness gap.

Analysis (Analyst): all five survive with `monotone`/`nlinarith`/`omega`
reasoning.  Deeper transference inequalities (`λ₁(L)·λ_d(L*) ≤ d`) need the dual
lattice and are *true but hard* at this abstraction level — flagged for
`FUTURE_DIRECTIONS`.

Critique (Critic): `sum_lam_ge/le` are non-trivial (they combine the min/max
lemmas with `Finset.sum_le_sum`); `sivp_factor_ge_one` extracts a genuine
inequality on `γ`.  None reduce to `rfl`/`decide`.

Synthesis (PI): the spectrum abstraction cleanly packages the worst-case side of
the reduction and feeds the parameter arithmetic in `RegevParameters.lean`.
-- !-- Lab Notes -- !--
-/

open Finset BigOperators

noncomputable section

/-- A `d`-dimensional lattice, abstracted by its successive-minima spectrum:
a strictly positive, monotone family `λ₁ ≤ λ₂ ≤ ⋯ ≤ λ_d`. -/
structure LatticeSpectrum (d : ℕ) where
  /-- The successive minima `λ₁, …, λ_d`. -/
  lam : Fin d → ℝ
  /-- Every successive minimum is strictly positive. -/
  pos : ∀ i, 0 < lam i
  /-- The successive minima are nondecreasing. -/
  mono : Monotone lam

namespace LatticeSpectrum

variable {d : ℕ} (L : LatticeSpectrum d)

/-- The first minimum `λ₁`, the length of a shortest nonzero lattice vector. -/
def lambda1 (hd : 0 < d) : ℝ := L.lam ⟨0, hd⟩

/-- The last minimum `λ_d`, the smallest radius containing `d` independent
lattice vectors. -/
def lambdaN (hd : 0 < d) : ℝ := L.lam ⟨d - 1, by omega⟩








/-! ## GapSVP: the decisional approximate shortest vector problem -/

/-- A `GapSVP_γ` YES instance (relative to threshold `β`): the shortest vector has
length at most `β`. -/
def GapSVPyes (hd : 0 < d) (β : ℝ) : Prop := L.lambda1 hd ≤ β

/-- A `GapSVP_γ` NO instance (relative to threshold `β`): the shortest vector has
length strictly greater than `γ·β`. -/
def GapSVPno (hd : 0 < d) (β γ : ℝ) : Prop := γ * β < L.lambda1 hd


/-! ## SIVP: the shortest independent vectors problem -/

/-- A candidate solution to `SIVP_γ`: a bundle of `d` independent lattice vectors,
recorded by their maximum length `maxLen`.  Independence forces the max length to
be at least `λ_d`; the `SIVP_γ` guarantee caps it at `γ·λ_d`. -/
structure SIVPSolution (hd : 0 < d) (γ : ℝ) where
  /-- The largest length among the `d` returned independent vectors. -/
  maxLen : ℝ
  /-- Independence lower bound: `d` independent vectors reach out to at least
  `λ_d`. -/
  indep_lb : L.lambdaN hd ≤ maxLen
  /-- Approximation guarantee: all returned vectors are within `γ·λ_d`. -/
  approx_ub : maxLen ≤ γ * L.lambdaN hd


/-! ## BDD: the average-case decoding target -/


end LatticeSpectrum

end



-- Prove2me | solution 1 for Teichmuller.spectrumValue_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:38:52.499242+00:00
-- url     : https://prove2.me/submissions/e60a956d-2c75-4002-90ca-88193128c641

-- Sol generated from Geometry/Teichmuller/LengthSpectrum.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LengthSpectrum
import Definitions.Def_Geometry_Teichmuller_TranslationLength
import Theorems.Thm_Teichmuller_cosh_log_stretchOf
/-
# The Teichmüller length spectrum of the torus

`Geometry.Teichmuller.TranslationLength` computes the Teichmüller translation length of a single
Anosov mapping class: for `g ∈ SL(2, ℤ)` with `|tr g| > 2` the minimal displacement
`min_τ d_T(τ, g · τ)` is attained and equals `log λ(g)` with
`λ(g) = (|tr g| + √(tr g² − 4)) / 2`, and every such trace is an integer of absolute value
at least `3`.

This file determines the **length spectrum** — the set of all these numbers — completely.
It is conjecture **C2** of `FUTURE_DIRECTIONS.md`.  Writing

    spectrumValue n = log ((n + √(n² − 4)) / 2)   (n ∈ ℤ, n ≥ 3),

the results are:

* `Teichmuller.tr_anosovClass`, `Teichmuller.isLeast_teichDist_anosovClass` : every integer
  `n ≥ 3` is realized, by the explicit Anosov class `!![n, −1; 1, 0]`;
* `Teichmuller.mem_lengthSpectrum_iff` : **the spectrum is exactly**
  `{ spectrumValue n : n ∈ ℤ, n ≥ 3 }`;
* `Teichmuller.spectrumValue_strictMonoOn` : the parametrization is strictly increasing, so the
  spectrum is order-isomorphic to `ℤ ∩ [3, ∞)`;
* `Teichmuller.abs_tr_le_of_log_stretch_le` : a translation length `≤ M` forces `|tr g| ≤ 2 e^M`,
  whence `Teichmuller.finite_lengthSpectrum_le` : **the spectrum is discrete** — only finitely
  many translation lengths lie below any bound;
* `Teichmuller.lengthSpectrum_unbounded` : the spectrum is unbounded;
* `Teichmuller.spectrumValue_three_eq_catMap`, together with
  `TranslationLength.goldenRatio_sq_le_stretch`, identifies the bottom of the spectrum as
  `log ((3 + √5)/2)`, the length of Arnold's cat map.

-- !-- Lab Notes -- !--
Hypothesizer (C2): the spectrum should be `{log ((t+√(t²−4))/2) : t ∈ ℤ, t ≥ 3}` — a metric
invariant computed by an arithmetic one.
Experimenter: realization needs one explicit matrix family; `!![t, −1; 1, 0]` has determinant
`1` and trace `t`, so no case analysis on `t` is required.  The converse inclusion is
`three_le_abs_tr` plus the observation that `stretch g` depends on `g` only through `|tr g|`.
Discreteness comes from `stretch_add_inv` (`λ + λ⁻¹ = |tr|`), which converts a bound on the
length into a bound on the trace; this is sharper than the compactness argument one would use
in general and gives the explicit constant `2 e^M`.
Analyst: the spectrum is therefore a *closed, discrete, unbounded* subset of `(0, ∞)` with least
element `log((3+√5)/2)`, and its `n`-th element is `arcosh(n/2)`; the counting function is
`#{n ≥ 3 : arcosh(n/2) ≤ L} = ⌊2 cosh L⌋ − 2 ∼ e^L`, matching the growth predicted in C2.
Critic: `mem_lengthSpectrum_iff` is an honest iff, both directions with content: `←` requires
building the matrix, `→` requires that the trace is an integer *and* that `stretch` factors
through `|tr|`.  No statement here is about a single example.
-/

open Teichmuller

open Complex UpperHalfPlane Matrix MatrixGroups









/-! ### Order structure: strict monotonicity, discreteness, unboundedness -/

theorem spectrumValue_pos {n : ℤ} (hn : 3 ≤ n) : 0 < spectrumValue n := by
  have hnn : (3:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (0:ℝ) ≤ (n : ℝ) ^ 2 - 4 := by nlinarith
  have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) ^ 2 - 4) := Real.sqrt_nonneg _
  rw [spectrumValue]
  exact Real.log_pos (by linarith)





/-! ### Concavity of the spectrum and its counting function -/


theorem cosh_spectrumValue {n : ℤ} (hn : 3 ≤ n) : Real.cosh (spectrumValue n) = (n : ℝ) / 2 := by
  have hx : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (2:ℤ) ≤ n)
  exact (cosh_log_stretchOf hx).1









open Teichmuller in
theorem solution{n : ℤ} (hn : 3 ≤ n) {L : ℝ} (hL : 0 ≤ L) :
    spectrumValue n ≤ L ↔ n ≤ ⌊2 * Real.cosh L⌋ := by
  have hpos : 0 < spectrumValue n := spectrumValue_pos hn
  constructor
  · intro h
    have hcosh : Real.cosh (spectrumValue n) ≤ Real.cosh L := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hpos.le, abs_of_nonneg hL]
      exact h
    rw [cosh_spectrumValue hn] at hcosh
    exact Int.le_floor.mpr (by linarith)
  · intro h
    have hle : (n : ℝ) ≤ 2 * Real.cosh L := by
      have h1 : ((n : ℤ) : ℝ) ≤ ((⌊2 * Real.cosh L⌋ : ℤ) : ℝ) := by exact_mod_cast h
      have h2 : ((⌊2 * Real.cosh L⌋ : ℤ) : ℝ) ≤ 2 * Real.cosh L := Int.floor_le _
      linarith
    have hcosh : Real.cosh (spectrumValue n) ≤ Real.cosh L := by
      rw [cosh_spectrumValue hn]; linarith
    have := Real.cosh_le_cosh.mp hcosh
    rwa [abs_of_nonneg hpos.le, abs_of_nonneg hL] at this

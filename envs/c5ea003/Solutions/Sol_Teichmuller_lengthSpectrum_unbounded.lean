-- Prove2me | solution 1 for Teichmuller.lengthSpectrum_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:34:45.123983+00:00
-- url     : https://prove2.me/submissions/09c48f45-8d67-4938-bcc7-be6736928805

-- Sol generated from Geometry/Teichmuller/LengthSpectrum.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LengthSpectrum
import Definitions.Def_Geometry_Teichmuller_TranslationLength
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



@[simp] theorem tr_anosovClass (n : ℤ) : tr (anosovClass n) = (n : ℝ) := by
  simp [tr, entry, anosovClass]

theorem abs_tr_anosovClass {n : ℤ} (hn : 3 ≤ n) : 2 < |tr (anosovClass n)| := by
  rw [tr_anosovClass, abs_of_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ n))]
  exact_mod_cast (by omega : (2:ℤ) < n)

theorem stretch_anosovClass {n : ℤ} (hn : 3 ≤ n) :
    stretch (anosovClass n) = ((n : ℝ) + Real.sqrt ((n : ℝ) ^ 2 - 4)) / 2 := by
  have hnn : (0:ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (0:ℤ) ≤ n)
  rw [stretch, tr_anosovClass, abs_of_nonneg hnn]




/-! ### Order structure: strict monotonicity, discreteness, unboundedness -/






/-! ### Concavity of the spectrum and its counting function -/











open Teichmuller in
theorem solution(M : ℝ) :
    ∃ g : SL(2, ℤ), 2 < |tr g| ∧ M < Real.log (stretch g) := by
  set n : ℤ := max 3 (⌈2 * Real.exp M⌉ + 1) with hn
  have hn3 : 3 ≤ n := le_max_left _ _
  have hnbig : 2 * Real.exp M < (n : ℝ) := by
    have h1 : (⌈2 * Real.exp M⌉ : ℝ) + 1 ≤ (n : ℝ) := by
      have : (⌈2 * Real.exp M⌉ + 1 : ℤ) ≤ n := le_max_right _ _
      exact_mod_cast this
    have h2 : 2 * Real.exp M ≤ (⌈2 * Real.exp M⌉ : ℝ) := Int.le_ceil _
    linarith
  refine ⟨anosovClass n, abs_tr_anosovClass hn3, ?_⟩
  rw [stretch_anosovClass hn3]
  have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) ^ 2 - 4) := Real.sqrt_nonneg _
  have hexp : 0 < Real.exp M := Real.exp_pos M
  have hlow : Real.exp M < ((n : ℝ) + Real.sqrt ((n : ℝ) ^ 2 - 4)) / 2 := by linarith
  have := Real.log_lt_log hexp hlow
  rwa [Real.log_exp] at this

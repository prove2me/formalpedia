-- Prove2me | Theorems.Thm_Teichmuller_exists_spectrumValue_eq
-- name    : Teichmuller.exists_spectrumValue_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:55:28.5616+00:00
-- url     : https://prove2.me/theorems/1fcb1842-ab75-4720-b0b5-e435cc8eb815
-- title:
--   The stretch factor of a hyperbolic class depends only on the absolute value of its trace,
-- statement:
--   The stretch factor of a hyperbolic class depends only on the absolute value of its trace,
--   which is an integer `≥ 3`.
--
--   ```lean
--   theorem Teichmuller.exists_spectrumValue_eq(g : SL(2, ℤ)) (ht : 2 < |tr g|) :
--       ∃ n : ℤ, 3 ≤ n ∧ Real.log (stretch g) = spectrumValue n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Teichmuller/LengthSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Teichmuller/LengthSpectrum.lean#L80

-- Thm stub generated from Geometry/Teichmuller/LengthSpectrum.lean
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

theorem Teichmuller.exists_spectrumValue_eq(g : SL(2, ℤ)) (ht : 2 < |tr g|) :
    ∃ n : ℤ, 3 ≤ n ∧ Real.log (stretch g) = spectrumValue n := by sorry

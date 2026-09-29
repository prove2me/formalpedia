-- Prove2me | Definitions.Def_Algebra_HumpWindowGeometry
-- name    : Algebra_HumpWindowGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:20:48.197134+00:00
-- url     : https://prove2.me/theorems/87311483-0104-4a21-9311-cf2e92678276
-- title:
--   Aether Catalog definitions — Algebra_HumpWindowGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.HumpWindowGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/HumpWindowGeometry.lean by skeleton subtraction
import Mathlib
/-
# H0 window geometry: what the shape of `j² − N` can and cannot produce

Formal core of experiment **581** (paper 231), the *sole surviving registered
channel* after the composition carriers were eliminated arithmetically:

> `H0` — window / polynomial geometry of `j² − N` itself, interacting with the
> value sizes `v`.

## The empirical object

Across the sieve window the experiment measures a ratio profile `R = T/M`
(observed hits over model prediction) binned into `64` positions, normalised to
`x ∈ [0,1]`.  The measured profile is *concave with an interior maximum*:

  `R_first = .8371`, `R_peak = 1.2227 @ bin 33`, `R_last = .8935`,
  pooled quadratic-fit vertex `x = 0.5901` (independently `0.5896` in exp 579),
  fitted curvature `c = -0.105 … -0.44` in every resolvable stratum.

The question `H0` asks is whether the *geometry alone* — the fact that the sieve
polynomial is `v(j) = j² − N` on an interval of `j` — forces such a profile.

## The model formalised here

Write `r = √N`, let the window be `j = r + s` with `s` ranging over an interval,
and normalise by the window length `M`, `x = s/M`.  Then

  `v = j² − N = s(s + 2r) = M² · x(x + 2c)`,  `c = r/M > 0`,

so, up to an additive constant `2 log M`, the *log-size profile* of the window is

  `logSize c x = log x + log (x + 2c)`.

The reference ("model") profile against which `R` is read is affine in the
`j`-grid: the chord through the two window endpoints.  The interior deviation is
then exactly `gap (logSize c) a b`.

## What is proved

* `HumpWindowGeometry.strictConcaveOn_logSize` — the log-size profile of
  `j² − N` is **strictly concave** on the whole window.  This is the geometric
  content of `H0`.
* `HumpWindowGeometry.gap_pos_interior` — consequently the chord-referenced
  deviation is **strictly one-signed in the interior and vanishes at both
  window edges**: the geometry does produce a hump, with edge deficits, exactly
  the qualitative shape measured.
* `HumpWindowGeometry.exists_isVertex`, `isVertex_unique`,
  `isMaxOn_gap_of_isVertex` — the hump has a **unique** vertex, characterised by
  `1/ξ + 1/(ξ + 2c) = ` chord slope, and the profile is strictly increasing to
  the left of it and strictly decreasing to the right.
* `HumpWindowGeometry.vertex_c_zero` — in the degenerate limit `c = 0` the
  vertex is the **logarithmic mean** of the endpoints.
* `HumpWindowGeometry.log_lt_iff_two_mul_sub_div` (`log_gt_two_mul_sub_div`) —
  the sharp inequality `2(t-1)/(t+1) < log t`, i.e. logarithmic mean strictly
  below arithmetic mean.
* `HumpWindowGeometry.vertex_lt_midpoint` — **the obstruction.**  For *every*
  admissible `N`, window and window length, the geometric vertex lies strictly
  to the **left** of the window centre.
* `HumpWindowGeometry.normalized_vertex_lt_half`,
  `measured_vertex_not_from_window_geometry` — the measured vertex `0.5901` is
  strictly to the *right* of centre, hence is **not** reproducible by the
  chord-referenced `H0` channel.  `H0` fragments: it explains the sign of the
  curvature and the two edge deficits, but it cannot place the vertex.
* `HumpWindowGeometry.quadratic_gap_vertex_eq_midpoint` — the contrasting
  control: a purely quadratic profile (no logarithm) puts the vertex exactly at
  the centre, so `0.5901` is not that either.
-/

namespace HumpWindowGeometry

open Set

/-! ## 1. The window value profile of `j² − N` -/

/-- The normalised value `v/M²` at relative window position `x`, where
`c = √N / M` is the window's aspect ratio: `j² − N = M² · x (x + 2c)`. -/
noncomputable def windowValue (c x : ℝ) : ℝ := x * (x + 2 * c)

/-- The log-size profile of the sieve window, normalised (`log v - 2 log M`). -/
noncomputable def logSize (c x : ℝ) : ℝ := Real.log x + Real.log (x + 2 * c)



/-! ## 2. Strict concavity: the geometric content of `H0` -/


/-! ## 3. Chord reference and the interior deviation -/

/-- The affine reference profile through the two window endpoints. -/
noncomputable def chord (f : ℝ → ℝ) (a b x : ℝ) : ℝ := f a + (x - a) / (b - a) * (f b - f a)

/-- The chord slope over the window. -/
noncomputable def chordSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ := (f b - f a) / (b - a)

/-- The interior deviation of a profile from its affine reference: the "hump". -/
noncomputable def gap (f : ℝ → ℝ) (a b x : ℝ) : ℝ := f x - chord f a b x







/-! ## 4. The vertex of the hump -/

/-- Derivative of the log-size profile: `1/x + 1/(x + 2c)`. -/
noncomputable def logSizeDeriv (c x : ℝ) : ℝ := 1 / x + 1 / (x + 2 * c)




/-- `ξ` is *the vertex* of the window hump on `[a,b]`: an interior point where
the log-size slope equals the chord slope. -/
def IsVertex (c a b ξ : ℝ) : Prop :=
  ξ ∈ Ioo a b ∧ logSizeDeriv c ξ = chordSlope (logSize c) a b







/-! ## 5. The sharp mean inequality -/



/-! ## 6. The obstruction: the geometric vertex is left of centre -/




/-! ## 7. Two calibrating special cases -/






end HumpWindowGeometry



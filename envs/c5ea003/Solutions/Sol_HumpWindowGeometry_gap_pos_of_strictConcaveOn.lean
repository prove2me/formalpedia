-- Prove2me | solution 1 for HumpWindowGeometry.gap_pos_of_strictConcaveOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:48:43.440545+00:00
-- url     : https://prove2.me/submissions/640675a0-ddb4-44c6-90de-f6f8d28df3af

-- Sol generated from Algebra/HumpWindowGeometry.lean
import Mathlib
import Definitions.Def_Algebra_HumpWindowGeometry
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

open HumpWindowGeometry

open Set

/-! ## 1. The window value profile of `j² − N` -/





/-! ## 2. Strict concavity: the geometric content of `H0` -/


/-! ## 3. Chord reference and the interior deviation -/










/-! ## 4. The vertex of the hump -/












/-! ## 5. The sharp mean inequality -/



/-! ## 6. The obstruction: the geometric vertex is left of centre -/




/-! ## 7. Two calibrating special cases -/







open HumpWindowGeometry in
theorem solution{f : ℝ → ℝ} {s : Set ℝ} (hf : StrictConcaveOn ℝ s f)
    {a b x : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hax : a < x) (hxb : x < b) :
    0 < gap f a b x := by
  have hab : a < b := lt_trans hax hxb
  have hba : (0 : ℝ) < b - a := by linarith
  set θ : ℝ := (b - x) / (b - a) with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) hba
  have hθ1 : 0 < 1 - θ := by
    have : θ < 1 := by
      rw [hθ, div_lt_one hba]; linarith
    linarith
  have hsum : θ + (1 - θ) = 1 := by ring
  have hcomb : θ * a + (1 - θ) * b = x := by
    rw [hθ]; field_simp; ring
  have hlt := hf.2 ha hb (by linarith) hθ0 hθ1 hsum
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hcomb] at hlt
  have hchord : chord f a b x = θ * f a + (1 - θ) * f b := by
    rw [chord, hθ]; field_simp; ring
  rw [gap, hchord]
  linarith

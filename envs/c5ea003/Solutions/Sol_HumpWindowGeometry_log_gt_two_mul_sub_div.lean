-- Prove2me | solution 1 for HumpWindowGeometry.log_gt_two_mul_sub_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:59:31.740414+00:00
-- url     : https://prove2.me/submissions/cb03e732-64b6-4c77-ac9c-7de1d0ad85c2

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
theorem solution{t : ℝ} (ht : 1 < t) : 2 * (t - 1) / (t + 1) < Real.log t := by
  set f : ℝ → ℝ := fun t => Real.log t - 2 * (t - 1) / (t + 1) with hf
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (1 / x - 4 / (x + 1) ^ 2) x := by
    intro x hx
    have hx1 : x + 1 ≠ 0 := by positivity
    have hnum : HasDerivAt (fun y : ℝ => 2 * (y - 1)) 2 x := by
      simpa using (((hasDerivAt_id x).sub_const 1).const_mul (2 : ℝ))
    have hden : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
    have hdiv : HasDerivAt (fun y : ℝ => 2 * (y - 1) / (y + 1))
        ((2 * (x + 1) - 2 * (x - 1) * 1) / (x + 1) ^ 2) x := hnum.div hden hx1
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
    have := hlog.sub hdiv
    convert this using 1
    field_simp
    ring
  have hmono : StrictMonoOn f (Ici (1 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      exact ((hderiv x hx0).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      rw [(hderiv x hx0).deriv]
      have hkey : 1 / x - 4 / (x + 1) ^ 2 = (x - 1) ^ 2 / (x * (x + 1) ^ 2) := by
        field_simp; ring
      rw [hkey]
      have h1 : (0 : ℝ) < (x - 1) ^ 2 := by
        have : x - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; exact absurd h (ne_of_gt hx)
        positivity
      positivity
  have h0 : f 1 = 0 := by simp [hf]
  have := hmono Set.self_mem_Ici (mem_Ici.2 (le_of_lt ht)) ht
  rw [h0] at this
  simp only [hf] at this
  linarith

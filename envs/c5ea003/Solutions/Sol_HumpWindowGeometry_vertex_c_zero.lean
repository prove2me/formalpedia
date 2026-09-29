-- Prove2me | solution 1 for HumpWindowGeometry.vertex_c_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:02:01.83626+00:00
-- url     : https://prove2.me/submissions/1534c9c3-892c-43c4-9e1e-5d7a43d49032

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


theorem hasDerivAt_logSize {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) :
    HasDerivAt (logSize c) (logSizeDeriv c x) x := by
  have h2 : 0 < x + 2 * c := by linarith
  have hL : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have hR : HasDerivAt (fun y : ℝ => Real.log (y + 2 * c)) (x + 2 * c)⁻¹ x := by
    have hinner : HasDerivAt (fun y : ℝ => y + 2 * c) 1 x := (hasDerivAt_id x).add_const _
    simpa using (Real.hasDerivAt_log (ne_of_gt h2)).comp x hinner
  simpa [logSize, logSizeDeriv, one_div] using hL.add hR


theorem continuousOn_logSize {c : ℝ} (hc : 0 ≤ c) :
    ContinuousOn (logSize c) (Ioi (0 : ℝ)) := fun _ hx =>
  ((hasDerivAt_logSize hc (mem_Ioi.1 hx)).continuousAt).continuousWithinAt


/-- **The vertex exists** (mean value theorem on the window). -/
theorem exists_isVertex {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hab : a < b) :
    ∃ ξ, IsVertex c a b ξ := by
  have hcont : ContinuousOn (logSize c) (Icc a b) :=
    (continuousOn_logSize hc).mono (fun x hx => mem_Ioi.2 (lt_of_lt_of_le ha hx.1))
  have hder : ∀ x ∈ Ioo a b, HasDerivAt (logSize c) (logSizeDeriv c x) x := fun x hx =>
    hasDerivAt_logSize hc (lt_trans ha hx.1)
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (logSize c) (logSizeDeriv c) hab hcont hder
  exact ⟨ξ, hξ, hslope⟩






/-! ## 5. The sharp mean inequality -/



/-! ## 6. The obstruction: the geometric vertex is left of centre -/




/-! ## 7. Two calibrating special cases -/







open HumpWindowGeometry in
theorem solution{a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsVertex 0 a b ((b - a) / (Real.log b - Real.log a)) := by
  have hq : 0 < b := lt_trans ha hab
  have hlogpos : 0 < Real.log b - Real.log a := by
    have := Real.log_lt_log ha hab
    linarith
  obtain ⟨ξ, hξ⟩ := exists_isVertex (le_refl (0 : ℝ)) ha hab
  have hξ0 : (0 : ℝ) < ξ := lt_trans ha hξ.1.1
  have hslope : chordSlope (logSize 0) a b = 2 * (Real.log b - Real.log a) / (b - a) := by
    rw [chordSlope, logSize, logSize]
    have h1 : a + 2 * (0 : ℝ) = a := by ring
    have h2 : b + 2 * (0 : ℝ) = b := by ring
    rw [h1, h2]
    ring
  have hd : logSizeDeriv 0 ξ = 2 / ξ := by
    rw [logSizeDeriv]
    have h : ξ + 2 * (0 : ℝ) = ξ := by ring
    rw [h]
    ring
  have heq : (2 : ℝ) / ξ = 2 * (Real.log b - Real.log a) / (b - a) := by
    rw [← hd, hξ.2, hslope]
  have hba : (0 : ℝ) < b - a := by linarith
  have hcross : (2 : ℝ) * (b - a) = 2 * (Real.log b - Real.log a) * ξ :=
    (div_eq_div_iff (ne_of_gt hξ0) (ne_of_gt hba)).1 heq
  have hL : ξ = (b - a) / (Real.log b - Real.log a) := by
    rw [eq_div_iff (ne_of_gt hlogpos)]
    linear_combination -hcross / 2
  rw [← hL]
  exact hξ

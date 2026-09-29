-- Prove2me | solution 1 for HumpVertexRigidity.log_lt_half_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:51:21.363646+00:00
-- url     : https://prove2.me/submissions/429dedde-8e49-4d8f-90a4-6ce9910ffa71

-- Sol generated from Algebra/HumpVertexRigidity.lean
import Mathlib
import Definitions.Def_Algebra_HumpVertexRigidity
import Definitions.Def_Algebra_HumpWindowGeometry
/-
# Rigidity of the hump vertex: a two-sided pin, independent of the aspect ratio

Fourth formal core of experiment **581** (paper 231), closing the first named
open question of the previous cycle.

`Algebra.HumpWindowGeometry` shows that the chord-gap vertex `ξ` of the log-size
profile of `j² − N` is unique and lies strictly left of the window centre.  What
it does not explain is a striking numerical fact: **the vertex barely moves when
the aspect ratio `c = √N / M` is varied over nine orders of magnitude.**

This file explains it, by pinning the vertex between two explicit logarithmic
means:

```
        LM(a, b)   ≤   ξ   ≤   LM(a + 2c, b + 2c) − 2c   <   (a + b)/2 ,
        LM(p, q) = (q − p) / (log q − log p).
```

Both bounds come from one monotonicity — that the logarithmic mean gains
*strictly more* than a common shift of its endpoints — and that in turn comes
from the classical `GM < LM` inequality, proved here from scratch.

## Main results

* `HumpVertexRigidity.log_lt_half_sub_inv` — `log s < (s − 1/s)/2` for `s > 1`.
* `HumpVertexRigidity.geomMean_mul_log_lt_sub` — **`GM < LM`**:
  `√(pq) · (log q − log p) < q − p` for `0 < p < q`.
* `HumpVertexRigidity.logMean_shift_le` — **shift rigidity**:
  `LM(a,b) + t ≤ LM(a+t, b+t)` for `t ≥ 0`.
* `HumpVertexRigidity.logMean_le_vertex` — the **lower** pin `LM(a,b) ≤ ξ`.
* `HumpVertexRigidity.vertex_le_shifted_logMean` — the **upper** pin
  `ξ ≤ LM(a+2c, b+2c) − 2c`.
* `HumpVertexRigidity.vertex_mem_Icc` — the two-sided pin, and
  `HumpVertexRigidity.vertex_indep_of_aspect` — the resulting bound on how far
  two vertices at different aspect ratios can be apart.

## Consequence for the verdict

The vertex of the geometric hump is not a free parameter of the sieve: it is
squeezed between two logarithmic means of the window endpoints.  In the sieve
regime `a = 1/M`, `b = 1` the lower pin is `≈ 1/log M`, so the geometric vertex
sits *near the left edge* and is pushed there harder as the window grows.  This
is the quantitative form of `HumpWindowGeometry.measured_vertex_not_from_window_geometry`:
the measured `0.5901` is not a near miss.
-/

open HumpVertexRigidity

open Set HumpWindowGeometry

/-! ## 1. `GM < LM` -/



/-! ## 2. Shift rigidity of the logarithmic mean -/




/-! ## 3. The two-sided pin on the vertex -/







open HumpVertexRigidity in
theorem solution{s : ℝ} (hs : 1 < s) : Real.log s < (s - 1 / s) / 2 := by
  set G : ℝ → ℝ := fun x => (x - 1 / x) / 2 - Real.log x with hG
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt G ((1 + 1 / x ^ 2) / 2 - 1 / x) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have h1 : HasDerivAt (fun y : ℝ => y - 1 / y) (1 - (-(1 / x ^ 2))) x := by
      have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
        simpa [one_div] using (hasDerivAt_inv hxne)
      exact (hasDerivAt_id x).sub hinv
    have h2 : HasDerivAt (fun y : ℝ => (y - 1 / y) / 2) ((1 - (-(1 / x ^ 2))) / 2) x :=
      h1.div_const 2
    have h3 : HasDerivAt Real.log (1 / x) x := by
      simpa [one_div] using Real.hasDerivAt_log hxne
    have := h2.sub h3
    convert this using 1
    ring
  have hmono : StrictMonoOn G (Ici (1 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro x hx
      exact ((hderiv x (lt_of_lt_of_le zero_lt_one hx)).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      rw [(hderiv x hx0).deriv]
      have hkey : (1 + 1 / x ^ 2) / 2 - 1 / x = (x - 1) ^ 2 / (2 * x ^ 2) := by
        field_simp
        ring
      rw [hkey]
      have hnum : (0 : ℝ) < (x - 1) ^ 2 := by
        have : x - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; exact absurd h (ne_of_gt hx)
        positivity
      positivity
  have h0 : G 1 = 0 := by simp [hG]
  have hlt := hmono Set.self_mem_Ici (mem_Ici.2 (le_of_lt hs)) hs
  rw [h0] at hlt
  simp only [hG] at hlt
  linarith

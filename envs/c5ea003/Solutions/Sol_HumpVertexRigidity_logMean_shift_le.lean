-- Prove2me | solution 1 for HumpVertexRigidity.logMean_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:56:12.708155+00:00
-- url     : https://prove2.me/submissions/539e57c7-ff0a-4015-8923-11c3c75c84b0

-- Sol generated from Algebra/HumpVertexRigidity.lean
import Mathlib
import Definitions.Def_Algebra_HumpVertexRigidity
import Definitions.Def_Algebra_HumpWindowGeometry
import Theorems.Thm_HumpVertexRigidity_geomMean_mul_log_lt_sub
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
theorem solution{a b : ℝ} (ha : 0 < a) (hab : a < b) {t : ℝ} (ht : 0 ≤ t) :
    logMean a b + t ≤ logMean (a + t) (b + t) := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp
  set d : ℝ := b - a with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set D : ℝ → ℝ := fun u => Real.log (b + u) - Real.log (a + u) with hD
  have hDpos : ∀ u : ℝ, 0 ≤ u → 0 < D u := by
    intro u hu
    have h1 : 0 < a + u := by linarith
    have h2 : a + u < b + u := by linarith
    have := Real.log_lt_log h1 h2
    rw [hD]; linarith
  have hDderiv : ∀ u : ℝ, 0 ≤ u → HasDerivAt D ((b + u)⁻¹ - (a + u)⁻¹) u := by
    intro u hu
    have h1 : (0 : ℝ) < a + u := by linarith
    have h2 : (0 : ℝ) < b + u := by linarith
    have hb : HasDerivAt (fun y : ℝ => Real.log (b + y)) ((b + u)⁻¹) u := by
      simpa using (Real.hasDerivAt_log (ne_of_gt h2)).comp u ((hasDerivAt_id u).const_add b)
    have haa : HasDerivAt (fun y : ℝ => Real.log (a + y)) ((a + u)⁻¹) u := by
      simpa using (Real.hasDerivAt_log (ne_of_gt h1)).comp u ((hasDerivAt_id u).const_add a)
    exact hb.sub haa
  set F : ℝ → ℝ := fun u => d / D u - u with hF
  have hFderiv : ∀ u : ℝ, 0 ≤ u →
      HasDerivAt F ((0 * D u - d * ((b + u)⁻¹ - (a + u)⁻¹)) / (D u) ^ 2 - 1) u := by
    intro u hu
    exact ((hasDerivAt_const u d).div (hDderiv u hu) (ne_of_gt (hDpos u hu))).sub
      (hasDerivAt_id u)
  have hmono : StrictMonoOn F (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro u hu
      exact ((hFderiv u (mem_Ici.1 hu)).continuousAt).continuousWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
      have h1 : (0 : ℝ) < a + u := by linarith
      have h2 : (0 : ℝ) < b + u := by linarith
      rw [(hFderiv u hu0).deriv]
      have hDu : 0 < D u := hDpos u hu0
      -- `GM < LM` for the shifted endpoints
      have hgm := geomMean_mul_log_lt_sub h1 (by linarith : a + u < b + u)
      have hDeq : Real.log (b + u) - Real.log (a + u) = D u := by rw [hD]
      rw [hDeq] at hgm
      have hsub : (b + u) - (a + u) = d := by rw [hd]; ring
      rw [hsub] at hgm
      have hsqrtpos : 0 < Real.sqrt ((a + u) * (b + u)) := Real.sqrt_pos.2 (by positivity)
      have hsq : Real.sqrt ((a + u) * (b + u)) ^ 2 = (a + u) * (b + u) :=
        Real.sq_sqrt (by positivity)
      have hkey : (a + u) * (b + u) * (D u) ^ 2 < d ^ 2 := by
        have hlhs : ((a + u) * (b + u)) * (D u) ^ 2
            = (Real.sqrt ((a + u) * (b + u)) * D u) ^ 2 := by
          rw [mul_pow, hsq]
        rw [hlhs]
        have hpos : 0 < Real.sqrt ((a + u) * (b + u)) * D u := mul_pos hsqrtpos hDu
        nlinarith [hgm, hpos]
      have hexp : (0 * D u - d * ((b + u)⁻¹ - (a + u)⁻¹)) / (D u) ^ 2 - 1
          = (d ^ 2 - (a + u) * (b + u) * (D u) ^ 2)
            / ((a + u) * (b + u) * (D u) ^ 2) := by
        field_simp
        ring
      rw [hexp]
      apply div_pos (by linarith) (by positivity)
  have hstep := hmono (mem_Ici.2 (le_refl 0)) (mem_Ici.2 ht) htpos
  simp only [hF] at hstep
  have hF0 : d / D 0 = logMean a b := by
    rw [hD, logMean, hd]
    norm_num
  have hFt : d / D t = logMean (a + t) (b + t) := by
    rw [hD, logMean, hd]
    have hsub : (b + t) - (a + t) = b - a := by ring
    rw [hsub]
  rw [hF0] at hstep
  rw [hFt] at hstep
  linarith

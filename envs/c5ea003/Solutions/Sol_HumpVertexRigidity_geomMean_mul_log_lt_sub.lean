-- Prove2me | solution 1 for HumpVertexRigidity.geomMean_mul_log_lt_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:53:59.378429+00:00
-- url     : https://prove2.me/submissions/0f406fa4-3dbe-4524-8634-0d7f783e63db

-- Sol generated from Algebra/HumpVertexRigidity.lean
import Mathlib
import Definitions.Def_Algebra_HumpVertexRigidity
import Definitions.Def_Algebra_HumpWindowGeometry
import Theorems.Thm_HumpVertexRigidity_log_lt_half_sub_inv
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
theorem solution{p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    Real.sqrt (p * q) * (Real.log q - Real.log p) < q - p := by
  have hq : 0 < q := lt_trans hp hpq
  set s : ℝ := Real.sqrt (q / p) with hs
  have hratio : 1 < q / p := (one_lt_div hp).2 hpq
  have hs1 : 1 < s := by
    rw [hs]
    have : Real.sqrt 1 < Real.sqrt (q / p) :=
      Real.sqrt_lt_sqrt (by norm_num) hratio
    simpa using this
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hssq : s ^ 2 = q / p := Real.sq_sqrt (le_of_lt (div_pos hq hp))
  have hq_eq : q = p * s ^ 2 := by
    rw [hssq]; field_simp
  have hsqrt : Real.sqrt (p * q) = p * s := by
    rw [hq_eq, hs]
    have hrw : p * (p * (Real.sqrt (q / p)) ^ 2) = (p * Real.sqrt (q / p)) ^ 2 := by ring
    rw [hrw, Real.sqrt_sq (by positivity)]
  have hlog : Real.log q - Real.log p = 2 * Real.log s := by
    rw [hq_eq, Real.log_mul (ne_of_gt hp) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hsqrt, hlog, hq_eq]
  have hkey := log_lt_half_sub_inv hs1
  have hstep : 2 * s * Real.log s < s ^ 2 - 1 := by
    have h2 : 2 * s * Real.log s < 2 * s * ((s - 1 / s) / 2) := by
      apply mul_lt_mul_of_pos_left hkey (by linarith)
    have hsimp : 2 * s * ((s - 1 / s) / 2) = s ^ 2 - 1 := by
      field_simp
    linarith [hsimp ▸ h2]
  nlinarith [hstep, hp]

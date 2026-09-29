-- Prove2me | solution 1 for HumpVertexRigidity.vertex_le_shifted_logMean
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:58:15.71609+00:00
-- url     : https://prove2.me/submissions/13f7b55c-fc23-4faa-ae06-098585f1166f

-- Sol generated from Algebra/HumpVertexRigidity.lean
import Mathlib
import Definitions.Def_Algebra_HumpVertexRigidity
import Definitions.Def_Algebra_HumpWindowGeometry
import Theorems.Thm_HumpVertexRigidity_chordSlope_split
import Theorems.Thm_HumpVertexRigidity_logMean_shift_le
import Theorems.Thm_HumpWindowGeometry_logSizeDeriv_strictAntiOn
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


theorem logMean_pos {p q : ℝ} (hp : 0 < p) (hpq : p < q) : 0 < logMean p q := by
  have hlog : 0 < Real.log q - Real.log p := by
    have := Real.log_lt_log hp hpq
    linarith
  exact div_pos (by linarith) hlog


/-! ## 3. The two-sided pin on the vertex -/







open HumpVertexRigidity in
theorem solution{c a b ξ : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hab : a < b)
    (hξ : IsVertex c a b ξ) : ξ ≤ logMean (a + 2 * c) (b + 2 * c) - 2 * c := by
  set L : ℝ := logMean a b with hL
  set L₂ : ℝ := logMean (a + 2 * c) (b + 2 * c) with hL2
  have hLpos : 0 < L := logMean_pos ha hab
  have hξ0 : (0 : ℝ) < ξ := lt_trans ha hξ.1.1
  have hshift : L + 2 * c ≤ L₂ := logMean_shift_le ha hab (by linarith)
  have hm2pos : 0 < L₂ - 2 * c := by linarith
  have hm2L : L ≤ L₂ - 2 * c := by linarith
  have hinv : 1 / (L₂ - 2 * c) ≤ 1 / L := one_div_le_one_div_of_le hLpos hm2L
  have hval : logSizeDeriv c (L₂ - 2 * c) = 1 / (L₂ - 2 * c) + 1 / L₂ := by
    rw [logSizeDeriv]
    have h : L₂ - 2 * c + 2 * c = L₂ := by ring
    rw [h]
  have hS : logSizeDeriv c (L₂ - 2 * c) ≤ chordSlope (logSize c) a b := by
    rw [hval, chordSlope_split ha hab hc, ← hL, ← hL2]
    linarith
  have hlt : logSizeDeriv c (L₂ - 2 * c) ≤ logSizeDeriv c ξ := by rw [hξ.2]; exact hS
  by_contra hcon
  push_neg at hcon
  exact absurd (logSizeDeriv_strictAntiOn hc (mem_Ioi.2 hm2pos) (mem_Ioi.2 hξ0) hcon)
    (not_lt.2 hlt)

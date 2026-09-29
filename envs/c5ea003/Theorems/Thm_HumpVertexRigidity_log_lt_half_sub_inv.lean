-- Prove2me | Theorems.Thm_HumpVertexRigidity_log_lt_half_sub_inv
-- name    : HumpVertexRigidity.log_lt_half_sub_inv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:38:52.155131+00:00
-- url     : https://prove2.me/theorems/af8bf875-bcc8-466c-9f69-ad5b2124cf4b
-- title:
--   `log s < (s - 1/s)/2` for `s > 1`.
-- statement:
--   `log s < (s - 1/s)/2` for `s > 1`.
--
--   ```lean
--   theorem HumpVertexRigidity.log_lt_half_sub_inv{s : ℝ} (hs : 1 < s) : Real.log s < (s - 1 / s) / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/HumpVertexRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/HumpVertexRigidity.lean#L55

-- Thm stub generated from Algebra/HumpVertexRigidity.lean
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

theorem HumpVertexRigidity.log_lt_half_sub_inv{s : ℝ} (hs : 1 < s) : Real.log s < (s - 1 / s) / 2 := by sorry

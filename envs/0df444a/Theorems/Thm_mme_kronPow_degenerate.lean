-- Prove2me | Theorems.Thm_mme_kronPow_degenerate
-- name    : mme_kronPow_degenerate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-28T20:42:24.541173+00:00
-- url     : https://prove2.me/theorems/e078c7e4-ac77-4222-baf2-1dfc31a8c439
-- statement:
--   **Degeneration is multiplicative under Kronecker powers.** If `X` degenerates from $I_r$ of order $h$, then $X^{\otimes m}$ degenerates from $I_{r^m}$ of order $m\cdot h$ (the $m$-fold Kronecker product of the witnessing polynomial family multiplies both the unit dimension and the vanishing order).
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_kronPow_degenerate {K : Type u} [Field K] {d : ℕ}
    {X : TensorObj K d} {r h : ℕ}
    (hdeg : DegeneratesOfOrder X (TensorObj.diagObj K d r) h) (m : ℕ) :
    DegeneratesOfOrder (TensorObj.kronPow X m) (TensorObj.diagObj K d (r ^ m)) (m * h) := by sorry

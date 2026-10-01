-- Prove2me | Theorems.Thm_Monotone_iUnion_Ioc_fin
-- name    : Monotone.iUnion_Ioc_fin
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:26:02.750537+00:00
-- url     : https://prove2.me/theorems/329625e5-f806-4adc-9620-f840c4c0f6f0
-- title:
--   Adjacent half-open intervals cover the range
-- statement:
--   For a monotone finite sequence of cuts, the union of adjacent $(c_i,c_{i+1}]$ equals $(c_0,c_{last}]$. Via biUnion_Ico_Ioc_map_succ and orderSucc_castSucc rewrites.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Order/IntervalPartition.lean#L11-L13

import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Order.Fin.Basic
open Set

namespace Monotone

theorem iUnion_Ioc_fin {α : Type*} [LinearOrder α] {n : ℕ} (cuts : Fin (n+1) → α) (hcuts : Monotone cuts) : (⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ)) = Ioc (cuts 0) (cuts (Fin.last n)) := by sorry

end Monotone

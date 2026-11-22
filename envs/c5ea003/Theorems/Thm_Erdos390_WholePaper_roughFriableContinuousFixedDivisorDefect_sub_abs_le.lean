-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughFriableContinuousFixedDivisorDefect_sub_abs_le
-- name    : Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect_sub_abs_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:58:34.946459+00:00
-- url     : https://prove2.me/theorems/929adea4-c066-4023-a6be-17ff9a15227d
-- title:
--   Interval cancellation for the continuous fixed-divisor Dickman defect
-- statement:
--   Let A,B,y,d be natural numbers with y≥2, 0<d≤A≤B and log B≤5 log y. Set u_X=log X/log y, t=log d/log y, and D(X)=X[ρ(u_X−t)−ρ(u_X)]/d, where ρ is the Dickman function used in the source. Then the continuous fixed-divisor defects at the two endpoints satisfy the interval-length bound below. It preserves cancellation before taking absolute values and is the continuous contribution to the fixed-head interval shift.
--
--   $$|D(B)-D(A)|\le\frac{(B-A)(\log d+2)}{d\log y}.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpFixedHeadIntervalShift.lean#L97-L256

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect_sub_abs_le : Erdos390.RemainingAnalyticGoal008_020 := by sorry

-- Prove2me | solution 2 for Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:08.395907+00:00
-- url     : https://prove2.me/submissions/ff7fd412-7f83-407d-8dd2-f34a47e19a85

import Mathlib
import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Theorems.Thm_Erdos390_WholePaper_roughFriableMain_abs_le_with_balanceError_compact

universe u_1

theorem solution :
    Erdos390.RemainingAnalyticGoal008_022.{u_1} :=
  Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError_compact

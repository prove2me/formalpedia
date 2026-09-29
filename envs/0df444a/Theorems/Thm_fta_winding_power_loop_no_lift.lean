-- Prove2me | Theorems.Thm_fta_winding_power_loop_no_lift
-- name    : fta_winding_power_loop_no_lift
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-05-22T15:00:13.27908+00:00
-- url     : https://prove2.me/theorems/f1c36c34-71d6-4667-856a-abc558167376
-- statement:
--   A positive-degree leading-term power loop has no continuous lift through the real exponential cover.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Definitions.Def_fta_winding_infra

theorem fta_winding_power_loop_no_lift (u : Circle) (n : ℕ) (hn : 0 < n) :
    ¬ FtaHasLift (FtaLeadingLoop u n) := by
  sorry

-- Prove2me | Theorems.Thm_robotMDP_vOpt
-- name    : robotMDP_vOpt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:41:23.763426+00:00
-- url     : https://prove2.me/theorems/d29abf8c-d485-47b2-a04e-d6a40856e869
-- title:
--   robot MDP v Opt: robot MDP v Opt
-- statement:
--   **The payoff.** `robotMDP`'s optimal value function is *exactly* the hand-solved vector, not
--       an approximation of it — checked by exhibiting it as a `bellman` fixed point and invoking
--       Banach uniqueness (Phase 2a), the same route `policyStep_fixedPoint_value_eq_vOpt` uses.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/RecyclingRobot.lean#L202-L254
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/RecyclingRobot.lean#L202-L254

import Definitions.Def_Mdp_PolicyIteration
import Definitions.Def_Mdp_RecyclingRobot
set_option autoImplicit true
open Mdp Mdp.DiscountedMDP

theorem robotMDP_vOpt : robotMDP.vOpt = robotV0 := by sorry

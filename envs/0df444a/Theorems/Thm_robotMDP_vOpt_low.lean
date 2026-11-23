-- Prove2me | Theorems.Thm_robotMDP_vOpt_low
-- name    : robotMDP_vOpt_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:41:42.599839+00:00
-- url     : https://prove2.me/theorems/9f256b08-977e-461a-8d13-c03bc2ae32ae
-- title:
--   robot MDP v Opt low: robot MDP v Opt low
-- statement:
--   The robot MDP v Opt low construction uses the robot MDP v Opt low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/RecyclingRobot.lean#L260-L261
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/RecyclingRobot.lean#L260-L261

import Definitions.Def_Mdp_PolicyIteration
import Definitions.Def_Mdp_RecyclingRobot
set_option autoImplicit true
open Mdp Mdp.DiscountedMDP

theorem robotMDP_vOpt_low : robotMDP.vOpt RobotState.low = 2 := by sorry

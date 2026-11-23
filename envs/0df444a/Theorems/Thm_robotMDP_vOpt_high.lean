-- Prove2me | Theorems.Thm_robotMDP_vOpt_high
-- name    : robotMDP_vOpt_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:41:17.826872+00:00
-- url     : https://prove2.me/theorems/dd41d23a-de9d-452c-8953-2ba33ad08152
-- title:
--   robot MDP v Opt high: robot MDP v Opt high
-- statement:
--   Corollaries in the shape someone skimming the file would actually want to see.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/RecyclingRobot.lean#L257-L258
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/RecyclingRobot.lean#L257-L258

import Definitions.Def_Mdp_PolicyIteration
import Definitions.Def_Mdp_RecyclingRobot
set_option autoImplicit true
open Mdp Mdp.DiscountedMDP

theorem robotMDP_vOpt_high : robotMDP.vOpt RobotState.high = 10 / 3 := by sorry

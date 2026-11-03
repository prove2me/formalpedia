-- Prove2me | Theorems.Thm_levy_foundations_cadlagAdd
-- name    : levy_foundations_cadlagAdd
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T12:38:11.357623+00:00
-- url     : https://prove2.me/theorems/87460449-5cd8-44b6-a927-9fdbc87512a7
-- title:
--   Addition preserves càdlàg paths
-- statement:
--   The pointwise sum of two real-valued càdlàg functions is càdlàg.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L144-L156. Closure under addition. Independently authored Prove2Me draft pending statement audit and remote compilation.

import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_levy_foundations_isCadlag

open Filter Set Topology
open scoped NNReal

theorem levy_foundations_cadlagAdd {f g : ℝ≥0 → ℝ}
    (hf : LevyFoundations.isCadlag f)
    (hg : LevyFoundations.isCadlag g) :
    LevyFoundations.isCadlag (fun t => f t + g t) := by sorry

-- Prove2me | Theorems.Thm_levy_foundations_jumpCountLtIff
-- name    : levy_foundations_jumpCountLtIff
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:37:30.362657+00:00
-- url     : https://prove2.me/theorems/64a78fc4-e895-4dc6-8a16-7be00891d854
-- title:
--   Characterise elapsed arrivals by jumpCount
-- statement:
--   Characterise elapsed arrivals by jumpCount.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean#L73

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
open Filter Set Topology

theorem levy_foundations_jumpCountLtIff
    (T : ℕ → ℝ) (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (n : ℕ) (t : ℝ) :
    n < LevyFoundations.jumpCount T t ↔ T n ≤ t := by sorry

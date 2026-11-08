-- Prove2me | Theorems.Thm_levy_foundations_piecewisePathAtZero
-- name    : levy_foundations_piecewisePathAtZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:38:29.102115+00:00
-- url     : https://prove2.me/theorems/41a5b6c7-a05f-46a7-8997-2900554cf14c
-- title:
--   Piecewise path begins at its initial value before the first arrival
-- statement:
--   Piecewise path begins at its initial value before the first arrival.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean#L125

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
open Filter Set Topology

theorem levy_foundations_piecewisePathAtZero
    {x₀ b : ℝ} {T Y : ℕ → ℝ} (hpos : 0 < T 0) :
    LevyFoundations.piecewisePath x₀ b T Y 0 = x₀ := by sorry

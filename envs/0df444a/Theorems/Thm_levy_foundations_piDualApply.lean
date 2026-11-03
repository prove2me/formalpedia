-- Prove2me | Theorems.Thm_levy_foundations_piDualApply
-- name    : levy_foundations_piDualApply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:00:01.338041+00:00
-- url     : https://prove2.me/theorems/ec7e0901-7740-4abe-bd01-3bb73870b45f
-- title:
--   Continuous dual of a finite real coordinate space acts by coordinate weights
-- statement:
--   A continuous real-linear functional of a finite real coordinate vector equals the finite sum of each coordinate multiplied by the functional's value on the corresponding unit vector. This identifies Fourier dual weights in the count-vector characteristic function.
-- source:
--   Independently formulated from the MIT-licensed LeanLevy PoissonPointFamily.lean private lemma pi_dual_apply at the pinned source commit 7e73fd9b23ad52956ec2756a815889a783131ce4. No mission-specific definitions required.

import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Probability.Independence.CharacteristicFunction

theorem levy_foundations_piDualApply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by sorry

-- Prove2me | Theorems.Thm_ef04_yosida_generation_proof_pointwise_upper_bound_8c6f7b69
-- name    : ef04_yosida_generation_proof_pointwise_upper_bound_8c6f7b69
-- status  : Open
-- author  : @WillR
-- created : 2026-11-05T15:21:15.185235+00:00
-- url     : https://prove2.me/theorems/c9a8d61d-d093-4f61-8250-09ee523ceaaa
-- title:
--   Dissipativity yields a Lipschitz resolvent bound
-- statement:
--   For every positive b, dissipativity applied to the difference of two elements of A' bounds b times the distance between their first coordinates by the distance between their b-resolvent values.

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open EthierKurtz MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

theorem ef04_yosida_generation_proof_pointwise_upper_bound_8c6f7b69
    {E : Type*}
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a →
      a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E))) 
    : ∀ b : ℝ, 0 < b →
      ∀ fg1 fg2 : UniformBoundedFunction E × UniformBoundedFunction E,
      ∀ h1 : fg1 ∈ A', ∀ h2 : fg2 ∈ A',
        b * ‖fg1.1 - fg2.1‖ ≤
          ‖(b • fg1.1 - fg1.2) - (b • fg2.1 - fg2.2)‖ := by sorry

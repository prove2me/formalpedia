-- Prove2me | solution 1 for Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:01:27.847716+00:00
-- url     : https://prove2.me/submissions/b173adef-7aea-40c3-b334-0a35edfb5ef8

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Theorems.Thm_Erdos390_Full_FixedFiniteMixtureFullUniform_exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact

universe u_1

theorem solution : Erdos390.RemainingAnalyticGoal001_001.{u_1} :=
  Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact.{u_1}

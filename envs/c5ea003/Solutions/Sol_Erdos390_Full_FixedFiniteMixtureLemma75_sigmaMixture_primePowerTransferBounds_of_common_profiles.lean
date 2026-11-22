-- Prove2me | solution 1 for Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:02:16.418711+00:00
-- url     : https://prove2.me/submissions/240333e3-02cd-4357-b71d-7c9660a5cfe9

import Mathlib
import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Theorems.Thm_Erdos390_Full_FixedFiniteMixtureLemma75_sigmaMixture_primePowerTransferBounds_of_common_profiles_compact

universe u_1 u_2

theorem solution :
    Erdos390.RemainingAnalyticGoal001_002.{u_1, u_2} :=
  Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles_compact

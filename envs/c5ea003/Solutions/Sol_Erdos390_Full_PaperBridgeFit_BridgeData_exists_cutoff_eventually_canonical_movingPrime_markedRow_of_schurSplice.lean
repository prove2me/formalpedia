-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T06:18:28.342876+00:00
-- url     : https://prove2.me/submissions/080ea652-2b33-4092-a744-6b29c089afe2

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact

universe u_1

theorem solution : Erdos390.RemainingAnalyticGoal001_014.{u_1} :=
  Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact.{u_1}

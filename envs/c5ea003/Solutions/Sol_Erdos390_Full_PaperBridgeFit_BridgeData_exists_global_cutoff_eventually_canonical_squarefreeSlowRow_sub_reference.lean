-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T18:48:55.903679+00:00
-- url     : https://prove2.me/submissions/3bd281c4-bc9b-4aa5-960d-0b77462e9e66

import Definitions.Def_erdos390_remaining_analytic_propositions_002
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference_compact

universe u_1

theorem solution : Erdos390.RemainingAnalyticGoal002_003.{u_1} :=
  Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference_compact.{u_1}

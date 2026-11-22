-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T06:16:55.471417+00:00
-- url     : https://prove2.me/submissions/bec6f8e0-c6e7-457b-aa2f-c2c62effefcf

import Definitions.Def_erdos390_remaining_analytic_propositions_002
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le_compact

universe u_1

theorem solution : Erdos390.RemainingAnalyticGoal002_002.{u_1} :=
  Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le_compact.{u_1}

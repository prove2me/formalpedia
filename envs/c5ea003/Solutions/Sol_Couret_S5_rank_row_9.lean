-- Prove2me | solution 1 for Couret.S5.rank_row_9
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:15:46.084494+00:00
-- url     : https://prove2.me/submissions/cd360d40-451d-431f-9b3a-7df4404f5f95

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5










theorem p2m_local_rank_row_9 : RankFacts 9 := by unfold RankFacts; decide +kernel






end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) := @_root_.Couret.S5.p2m_local_rank_row_9


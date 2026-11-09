-- Prove2me | solution 1 for Couret.S5.rank_row_124
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:08:39.065242+00:00
-- url     : https://prove2.me/submissions/f5504ecd-f5cb-42a7-a1d5-4e191867c48d

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5













theorem p2m_local_rank_row_124 : RankFacts 124 := by unfold RankFacts; decide +kernel



end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))) := @_root_.Couret.S5.p2m_local_rank_row_124


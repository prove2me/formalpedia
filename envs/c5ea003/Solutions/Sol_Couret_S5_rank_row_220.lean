-- Prove2me | solution 1 for Couret.S5.rank_row_220
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:12:43.01086+00:00
-- url     : https://prove2.me/submissions/e4ae58f3-930e-472d-a290-e5935c88a88e

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5













theorem p2m_local_rank_row_220 : RankFacts 220 := by unfold RankFacts; decide +kernel



end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 220) (instOfNatNat (nat_lit 220))) := @_root_.Couret.S5.p2m_local_rank_row_220


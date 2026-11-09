-- Prove2me | solution 1 for Couret.S5.rank_row_126
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:08:41.010208+00:00
-- url     : https://prove2.me/submissions/9aac1ed7-d69f-4373-9d90-6b4f37d925db

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5















theorem p2m_local_rank_row_126 : RankFacts 126 := by unfold RankFacts; decide +kernel

end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126))) := @_root_.Couret.S5.p2m_local_rank_row_126


-- Prove2me | solution 1 for Couret.S5.rank_row_188
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:11:46.35221+00:00
-- url     : https://prove2.me/submissions/2d9f03b1-09e8-431a-a59b-e99c37e29332

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5













theorem p2m_local_rank_row_188 : RankFacts 188 := by unfold RankFacts; decide +kernel



end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))) := @_root_.Couret.S5.p2m_local_rank_row_188


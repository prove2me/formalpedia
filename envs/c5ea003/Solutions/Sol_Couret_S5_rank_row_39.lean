-- Prove2me | solution 1 for Couret.S5.rank_row_39
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:14:19.43794+00:00
-- url     : https://prove2.me/submissions/703a15a8-eb92-498a-bb66-4422a5af9b0a

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5








theorem p2m_local_rank_row_39 : RankFacts 39 := by unfold RankFacts; decide +kernel








end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 39) (instOfNatNat (nat_lit 39))) := @_root_.Couret.S5.p2m_local_rank_row_39


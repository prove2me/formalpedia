-- Prove2me | solution 1 for Couret.S5.rank_row_130
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:09:03.209009+00:00
-- url     : https://prove2.me/submissions/7fa55b28-54a2-4f6d-ba77-3a4863e10070

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5



theorem p2m_local_rank_row_130 : RankFacts 130 := by unfold RankFacts; decide +kernel













end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) := @_root_.Couret.S5.p2m_local_rank_row_130


-- Prove2me | solution 1 for Couret.S5.rank_row_136
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:09:57.063971+00:00
-- url     : https://prove2.me/submissions/52bac7c6-7a99-4b81-99a2-8e404ef353a6

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5









theorem p2m_local_rank_row_136 : RankFacts 136 := by unfold RankFacts; decide +kernel







end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 136) (instOfNatNat (nat_lit 136))) := @_root_.Couret.S5.p2m_local_rank_row_136


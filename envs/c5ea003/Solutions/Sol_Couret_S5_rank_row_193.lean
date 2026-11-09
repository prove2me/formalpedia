-- Prove2me | solution 1 for Couret.S5.rank_row_193
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:11:58.531325+00:00
-- url     : https://prove2.me/submissions/bd9579de-4a0b-4afb-b4f7-4101ff9a2ea4

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5


theorem p2m_local_rank_row_193 : RankFacts 193 := by unfold RankFacts; decide +kernel














end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 193) (instOfNatNat (nat_lit 193))) := @_root_.Couret.S5.p2m_local_rank_row_193


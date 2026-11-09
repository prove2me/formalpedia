-- Prove2me | solution 1 for Couret.S5.rank_row_2
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:12:07.259201+00:00
-- url     : https://prove2.me/submissions/369e8539-8f68-4479-9644-20d9f91d52a0

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5



theorem p2m_local_rank_row_2 : RankFacts 2 := by unfold RankFacts; decide +kernel













end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) := @_root_.Couret.S5.p2m_local_rank_row_2


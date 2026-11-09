-- Prove2me | solution 1 for Couret.S5.rank_row_1
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:06:03.264206+00:00
-- url     : https://prove2.me/submissions/fddd2654-4ed4-48dd-88a3-fed2a08ccc92

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5


theorem p2m_local_rank_row_1 : RankFacts 1 := by unfold RankFacts; decide +kernel














end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.S5.p2m_local_rank_row_1


-- Prove2me | solution 1 for Couret.S5.rank_row_3
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:13:53.596853+00:00
-- url     : https://prove2.me/submissions/89c43215-6819-470b-91ea-985b79d1b0b3

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5




theorem p2m_local_rank_row_3 : RankFacts 3 := by unfold RankFacts; decide +kernel












end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) := @_root_.Couret.S5.p2m_local_rank_row_3


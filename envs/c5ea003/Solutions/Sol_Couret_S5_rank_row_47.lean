-- Prove2me | solution 1 for Couret.S5.rank_row_47
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:14:44.657641+00:00
-- url     : https://prove2.me/submissions/1f78e2a5-c842-4610-b228-bb3db56d77a6

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5
















theorem p2m_local_rank_row_47 : RankFacts 47 := by unfold RankFacts; decide +kernel
end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 47) (instOfNatNat (nat_lit 47))) := @_root_.Couret.S5.p2m_local_rank_row_47


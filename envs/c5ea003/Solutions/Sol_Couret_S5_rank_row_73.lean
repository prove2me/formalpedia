-- Prove2me | solution 1 for Couret.S5.rank_row_73
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:15:16.626029+00:00
-- url     : https://prove2.me/submissions/12d04098-0966-47a2-8458-8bf19cb390e1

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5










theorem p2m_local_rank_row_73 : RankFacts 73 := by unfold RankFacts; decide +kernel






end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 73) (instOfNatNat (nat_lit 73))) := @_root_.Couret.S5.p2m_local_rank_row_73


-- Prove2me | solution 1 for Couret.S5.rank_row_111
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:08:03.893345+00:00
-- url     : https://prove2.me/submissions/a8025770-5011-4e67-899a-08fcfaaf7c04

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5
















theorem p2m_local_rank_row_111 : RankFacts 111 := by unfold RankFacts; decide +kernel
end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 111) (instOfNatNat (nat_lit 111))) := @_root_.Couret.S5.p2m_local_rank_row_111


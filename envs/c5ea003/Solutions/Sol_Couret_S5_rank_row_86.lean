-- Prove2me | solution 1 for Couret.S5.rank_row_86
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:15:42.025907+00:00
-- url     : https://prove2.me/submissions/6c23c0b5-0f1a-4598-8311-9e6d27950646

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5







theorem p2m_local_rank_row_86 : RankFacts 86 := by unfold RankFacts; decide +kernel









end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 86) (instOfNatNat (nat_lit 86))) := @_root_.Couret.S5.p2m_local_rank_row_86


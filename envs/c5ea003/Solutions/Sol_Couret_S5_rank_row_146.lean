-- Prove2me | solution 1 for Couret.S5.rank_row_146
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:10:25.239603+00:00
-- url     : https://prove2.me/submissions/a3fda62c-f247-4ad3-9613-7c5a944e61b8

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5



theorem p2m_local_rank_row_146 : RankFacts 146 := by unfold RankFacts; decide +kernel













end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146))) := @_root_.Couret.S5.p2m_local_rank_row_146


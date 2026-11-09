-- Prove2me | solution 1 for Couret.S5.rank_row_195
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:12:01.519165+00:00
-- url     : https://prove2.me/submissions/a8e50c54-0199-4cc2-b046-20da5554f89c

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5




theorem p2m_local_rank_row_195 : RankFacts 195 := by unfold RankFacts; decide +kernel












end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 195) (instOfNatNat (nat_lit 195))) := @_root_.Couret.S5.p2m_local_rank_row_195


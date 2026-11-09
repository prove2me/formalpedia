-- Prove2me | solution 1 for Couret.S5.rank_row_213
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:12:26.837752+00:00
-- url     : https://prove2.me/submissions/5fe6f1bf-af45-4294-9fec-81071b44ace0

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5






theorem p2m_local_rank_row_213 : RankFacts 213 := by unfold RankFacts; decide +kernel










end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 213) (instOfNatNat (nat_lit 213))) := @_root_.Couret.S5.p2m_local_rank_row_213


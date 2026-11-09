-- Prove2me | solution 1 for Couret.S5.rank_row_113
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:08:12.641604+00:00
-- url     : https://prove2.me/submissions/db5a6a0b-9b4b-4a79-ac4d-4636f9a5282e

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5


theorem p2m_local_rank_row_113 : RankFacts 113 := by unfold RankFacts; decide +kernel














end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 113) (instOfNatNat (nat_lit 113))) := @_root_.Couret.S5.p2m_local_rank_row_113


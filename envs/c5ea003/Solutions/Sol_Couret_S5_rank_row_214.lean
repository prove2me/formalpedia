-- Prove2me | solution 1 for Couret.S5.rank_row_214
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:12:27.088329+00:00
-- url     : https://prove2.me/submissions/bfd8a222-6d85-4e1b-a9a8-f60e1d1274f5

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5







theorem p2m_local_rank_row_214 : RankFacts 214 := by unfold RankFacts; decide +kernel









end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 214) (instOfNatNat (nat_lit 214))) := @_root_.Couret.S5.p2m_local_rank_row_214


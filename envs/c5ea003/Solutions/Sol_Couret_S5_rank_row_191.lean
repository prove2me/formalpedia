-- Prove2me | solution 1 for Couret.S5.rank_row_191
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:11:56.812887+00:00
-- url     : https://prove2.me/submissions/e2349674-1a9f-48ef-bbbd-008e0df72b18

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5
















theorem p2m_local_rank_row_191 : RankFacts 191 := by unfold RankFacts; decide +kernel
end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 191) (instOfNatNat (nat_lit 191))) := @_root_.Couret.S5.p2m_local_rank_row_191


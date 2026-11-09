-- Prove2me | solution 1 for Couret.S5.rank_row_253
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:13:43.989977+00:00
-- url     : https://prove2.me/submissions/c47e1646-3a7a-4e2b-b089-7dcdb795b617

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5














theorem p2m_local_rank_row_253 : RankFacts 253 := by unfold RankFacts; decide +kernel


end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 253) (instOfNatNat (nat_lit 253))) := @_root_.Couret.S5.p2m_local_rank_row_253


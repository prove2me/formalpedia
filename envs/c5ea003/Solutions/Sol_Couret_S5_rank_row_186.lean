-- Prove2me | solution 1 for Couret.S5.rank_row_186
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:11:45.098439+00:00
-- url     : https://prove2.me/submissions/72eb4902-399c-4ea6-bdb6-a3d0d38889c2

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5











theorem p2m_local_rank_row_186 : RankFacts 186 := by unfold RankFacts; decide +kernel





end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 186) (instOfNatNat (nat_lit 186))) := @_root_.Couret.S5.p2m_local_rank_row_186


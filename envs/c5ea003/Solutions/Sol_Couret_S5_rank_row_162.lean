-- Prove2me | solution 1 for Couret.S5.rank_row_162
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:10:42.4716+00:00
-- url     : https://prove2.me/submissions/af00ab7d-c70e-48e5-8afb-35b242d8179d

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5



theorem p2m_local_rank_row_162 : RankFacts 162 := by unfold RankFacts; decide +kernel













end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) := @_root_.Couret.S5.p2m_local_rank_row_162


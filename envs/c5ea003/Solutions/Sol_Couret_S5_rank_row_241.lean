-- Prove2me | solution 1 for Couret.S5.rank_row_241
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:13:34.889201+00:00
-- url     : https://prove2.me/submissions/2ec2cf5b-237b-4578-adc4-825271a05be6

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5


theorem p2m_local_rank_row_241 : RankFacts 241 := by unfold RankFacts; decide +kernel














end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 241) (instOfNatNat (nat_lit 241))) := @_root_.Couret.S5.p2m_local_rank_row_241


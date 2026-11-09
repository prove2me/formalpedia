-- Prove2me | solution 1 for Couret.S5.rank_row_13
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:09:05.097403+00:00
-- url     : https://prove2.me/submissions/4eaacef5-8495-4cf5-9a7e-99fd47b6826c

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5














theorem p2m_local_rank_row_13 : RankFacts 13 := by unfold RankFacts; decide +kernel


end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) := @_root_.Couret.S5.p2m_local_rank_row_13


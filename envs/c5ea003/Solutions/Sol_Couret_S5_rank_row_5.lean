-- Prove2me | solution 1 for Couret.S5.rank_row_5
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:14:46.202347+00:00
-- url     : https://prove2.me/submissions/0f9449ab-2f90-4107-919c-4eab41bcc920

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5






theorem p2m_local_rank_row_5 : RankFacts 5 := by unfold RankFacts; decide +kernel










end S5
end Couret

theorem solution : Couret.S5.RankFacts (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) := @_root_.Couret.S5.p2m_local_rank_row_5


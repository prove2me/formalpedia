-- Prove2me | solution 1 for Couret.S5.rank_initial
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:14.380081+00:00
-- url     : https://prove2.me/submissions/b2bbd8be-97e3-4d94-bcb9-f89c8f5b85c1

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5
theorem p2m_local_rank_initial : rank 0 = 0 := by decide +kernel

end S5
end Couret

theorem solution : @Eq.{1} Nat (Couret.S5.rank (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := @_root_.Couret.S5.p2m_local_rank_initial


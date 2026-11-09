-- Prove2me | Definitions.Def_Couret_RankBlock00_bd2f9788729f
-- name    : Couret_RankBlock00_bd2f9788729f
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:45.001028+00:00
-- url     : https://prove2.me/theorems/a07aa87a-649d-45fc-bd31-6ddb4649eebe
-- title:
--   The subproduct rank-row contract
-- statement:
--   For a natural mask $m$, let $r(m)$ be its table rank, $S(m)$ its residue support and $T_g(m)$ the next subproduct mask. The row contract is $$r(m)\le5,\quad r(m)=5\iff(0,0)\in S(m),\quad\min(r(m)+1,5)\le r(T_g(m))\quad(\forall g).$$ It defines the finite invariant proved separately for each mask row.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock00.lean; source file SHA-256 5b5b79d47dbea03302241f73ec335797269838fe2f41d74a323693005f369d9b

import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5
def RankFacts (m : Nat) : Prop := rank m ≤ 5 ∧ (rank m = 5 ↔ maskSupport m (0,0)) ∧ ∀ g : Code30, min (rank m + 1) 5 ≤ rank (subStep m g)
















end S5
end Couret



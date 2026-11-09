-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_equal_rank_bank_surjective
-- name    : Couret.STROBO2TORS.recoh_equal_rank_bank_surjective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:38.415418+00:00
-- url     : https://prove2.me/theorems/99a98196-a86b-4fb6-bf36-d66e48316830
-- title:
--   An injective equal-rank binary bank is surjective
-- statement:
--   Let $H$ be a finite abelian group of size $2^r$, and $r$ additive maps $b_i:H\to\mathbb Z/2\mathbb Z$. If their joint map is injective, then
--
--   $$a\mapsto(b_i(a))_{i<r}\quad\text{is surjective onto }(\mathbb Z/2\mathbb Z)^r.$$
--
--   The case $r=0$ is allowed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/85df7268e792e69b2e1ad2461dec2af575c43c88/research/strobo-2tors-2026-10-12/lean/RecohEqualRank.lean#L14-L32, lines 14–32; source file SHA-256 145264824ba6e4556bc833bba9f6993ce5e3f8a2793764e8545cc893e5195340; theorem Couret.STROBO2TORS.recoh_equal_rank_bank_surjective

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-!
RECOH: the square (k=r) information-set case.
This avoids claiming any selection theorem for k > r.
-/

namespace Couret.STROBO2TORS

theorem recoh_equal_rank_bank_surjective
    {H : Type*} [AddCommGroup H] [Fintype H]
    (r : ℕ)
    (hcard : Fintype.card H = 2 ^ r)
    (bank : Fin r → H →+ ZMod 2)
    (hinj : Function.Injective
      (fun a : H => fun i : Fin r => bank i a)) :
    Function.Surjective
      (fun a : H => fun i : Fin r => bank i a) := by sorry


end Couret.STROBO2TORS

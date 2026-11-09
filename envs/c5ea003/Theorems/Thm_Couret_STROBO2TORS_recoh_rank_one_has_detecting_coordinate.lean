-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_rank_one_has_detecting_coordinate
-- name    : Couret.STROBO2TORS.recoh_rank_one_has_detecting_coordinate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:40.235359+00:00
-- url     : https://prove2.me/theorems/4f341783-863e-495f-9870-90cf9a02f524
-- title:
--   An injective binary bank detects the nonzero rank-one element
-- statement:
--   For any natural $k$ and additive maps $b_i:\mathbb Z/2\mathbb Z\to\mathbb Z/2\mathbb Z$, if the joint bank is injective, then
--
--   $$\exists i<k,\quad b_i(1)\ne0.$$
--
--   In particular an empty bank cannot be injective on this domain.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/71d66a9addc72a758b9d02ffad265c35cab94534/research/strobo-2tors-2026-10-12/lean/RecohRankOne.lean#L14-L31, lines 14–31; source file SHA-256 07da71eb8926527921cf51da12d15c9f546c2c883d038fc93b2c3819a8b907be; theorem Couret.STROBO2TORS.recoh_rank_one_has_detecting_coordinate

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

set_option autoImplicit false

/-!
RECOH rank-one information-set base case.
A genuinely injective binary bank on ZMod 2 must contain
at least one coordinate detecting the unique nonzero element.
This does NOT prove the higher-rank information-set lemma.
-/

namespace Couret.STROBO2TORS

theorem recoh_rank_one_has_detecting_coordinate
    (k : ℕ)
    (bank : Fin k → ZMod 2 →+ ZMod 2)
    (hinj : Function.Injective
      (fun x : ZMod 2 => fun i : Fin k => bank i x)) :
    ∃ i : Fin k, bank i (1 : ZMod 2) ≠ 0 := by sorry


end Couret.STROBO2TORS

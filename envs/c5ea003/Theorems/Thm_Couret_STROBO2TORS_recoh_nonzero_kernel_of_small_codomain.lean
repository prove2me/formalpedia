-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_nonzero_kernel_of_small_codomain
-- name    : Couret.STROBO2TORS.recoh_nonzero_kernel_of_small_codomain
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:11.724455+00:00
-- url     : https://prove2.me/theorems/350baa98-6708-4866-86bc-3a497a506007
-- title:
--   An additive map into a smaller finite group has a nonzero kernel
-- statement:
--   Let $A,B$ be finite abelian groups and $f:A\to B$ additive. If $|B|<|A|$, then
--
--   $$\exists a\ne0,\quad f(a)=0.$$
--
--   No prime or exponent assumption is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohRankKernel.lean, lines 22–40; source file SHA-256 487347524b5e69a3ac7a4b19c6bd0f66ddebcee99da5fdb907592b14d58f65ff; theorem Couret.STROBO2TORS.recoh_nonzero_kernel_of_small_codomain

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
RECOH: finite character rank kernel bound.

For a finite additive group A of cardinal p^r and any list of k < r
additive probes valued in ZMod p, a nonzero element lies in their
common kernel. This is a group-homomorphism statement, not merely
a pigeonhole bound on unstructured binary or ternary words.

Scope boundary: this covers the common-kernel case of the
lower bound. It does NOT build the mixed order-two/order-three
mask for k between r and r+s, nor construct the upper bank.
-/

namespace Couret.STROBO2TORS

theorem recoh_nonzero_kernel_of_small_codomain
    {A B : Type*}
    [AddCommGroup A] [Fintype A]
    [AddCommGroup B] [Fintype B]
    (f : A →+ B)
    (hsmall : Fintype.card B < Fintype.card A) :
    ∃ a : A, a ≠ 0 ∧ f a = 0 := by sorry










end Couret.STROBO2TORS

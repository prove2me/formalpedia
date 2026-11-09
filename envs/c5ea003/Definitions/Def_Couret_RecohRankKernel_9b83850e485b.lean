-- Prove2me | Definitions.Def_Couret_RecohRankKernel_9b83850e485b
-- name    : Couret_RecohRankKernel_9b83850e485b
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:51.109606+00:00
-- url     : https://prove2.me/theorems/e2425913-09bb-47e1-8093-0648c16d4ce9
-- title:
--   The joint modular character bank map
-- statement:
--   For an additive group $A$, a nonzero modulus $p$, and $k$ additive maps $A\to\mathbb Z/p\mathbb Z$, defines the additive map sending $a$ to the vector of all $k$ character values. This exposes the common kernel used in cardinality-based rank lower bounds.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohRankKernel.lean; source file SHA-256 487347524b5e69a3ac7a4b19c6bd0f66ddebcee99da5fdb907592b14d58f65ff

import Aesop
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



/-- A finite collection of additive probes is itself an additive map to
the vector of outcomes. This keeps the kernel argument compositional. -/
def recohModBankMap
    {A : Type*} [AddCommGroup A]
    (p k : ℕ) [NeZero p]
    (bank : Fin k → A →+ ZMod p) :
    A →+ (Fin k → ZMod p) where
  toFun a := fun i => bank i a
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp







end Couret.STROBO2TORS



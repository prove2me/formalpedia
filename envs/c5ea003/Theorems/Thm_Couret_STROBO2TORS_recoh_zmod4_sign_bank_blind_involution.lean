-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_zmod4_sign_bank_blind_involution
-- name    : Couret.STROBO2TORS.recoh_zmod4_sign_bank_blind_involution
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:42:31.008275+00:00
-- url     : https://prove2.me/theorems/7a919536-6f60-4660-ab4f-6dd66d683c86
-- title:
--   Sign-valued probes on the cyclic four-group miss its involution
-- statement:
--   Let $k\in\mathbb N$ and let $f_i:\mathbb Z/4\mathbb Z\to\mathbb C$ satisfy $f_i(a+b)=f_i(a)f_i(b)$ and $f_i(a)\in\{1,-1\}$ for all $i<k,a$. Then
--
--   $$2\ne0,\qquad2+2=0,\qquad f_i(2)=f_i(0)\quad(i<k).$$
--
--   Thus any number of sign-valued probes fails to distinguish this nonzero two-torsion element from zero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohUpperSignGate.lean, lines 55–78; source file SHA-256 23dbd7f039960c17878480e96b1f4e17296dead0ed739a90a6b9fd4ddfdf3034; theorem Couret.STROBO2TORS.recoh_zmod4_sign_bank_blind_involution

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
RECOH upper-bank prerequisite: sign-only character probes cannot suffice
in general. On ZMod 4, every multiplicative character valued in {1,-1}
annihilates the nonzero involution 2.

This is a formal obstruction, not a construction of the required
2-primary and 3-primary characters. No global B(G) theorem is claimed.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_zmod4_sign_bank_blind_involution
    (k : ℕ)
    (bank : Fin k → ZMod 4 → ℂ)
    (hadd : ∀ i : Fin k, ∀ a b : ZMod 4,
      bank i (a + b) = bank i a * bank i b)
    (hsign : ∀ i : Fin k, ∀ a : ZMod 4,
      bank i a = 1 ∨ bank i a = -1) :
    (2 : ZMod 4) ≠ 0 ∧
    (2 : ZMod 4) + 2 = 0 ∧
    (∀ i : Fin k, bank i (2 : ZMod 4) = bank i (0 : ZMod 4)) := by sorry




end Couret.STROBO2TORS

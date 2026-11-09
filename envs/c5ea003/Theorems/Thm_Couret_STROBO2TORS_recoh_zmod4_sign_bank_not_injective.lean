-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_zmod4_sign_bank_not_injective
-- name    : Couret.STROBO2TORS.recoh_zmod4_sign_bank_not_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:27.185437+00:00
-- url     : https://prove2.me/theorems/c0b25eee-9c95-4d53-aa27-053ccd4c829b
-- title:
--   Sign-valued characters cannot separate the cyclic group of order four
-- statement:
--   For any $k\in\mathbb N$, let $f_i:\mathbb Z/4\mathbb Z\to\mathbb C$ satisfy $f_i(a+b)=f_i(a)f_i(b)$ and $f_i(a)\in\{1,-1\}$ for every $i<k$ and $a$. Then
--
--   $$a\longmapsto(f_i(a))_{i<k}\quad\text{is not injective}.$$
--
--   No matter how many such sign-valued probes are used, zero and two have the same readings.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohUpperSignGate.lean, lines 80–100; source file SHA-256 23dbd7f039960c17878480e96b1f4e17296dead0ed739a90a6b9fd4ddfdf3034; theorem Couret.STROBO2TORS.recoh_zmod4_sign_bank_not_injective

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_zmod4_sign_bank_blind_involution
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

theorem recoh_zmod4_sign_bank_not_injective
    (k : ℕ)
    (bank : Fin k → ZMod 4 → ℂ)
    (hadd : ∀ i : Fin k, ∀ a b : ZMod 4,
      bank i (a + b) = bank i a * bank i b)
    (hsign : ∀ i : Fin k, ∀ a : ZMod 4,
      bank i a = 1 ∨ bank i a = -1) :
    ¬ Function.Injective
      (fun a : ZMod 4 => fun i : Fin k => bank i a) := by sorry


end Couret.STROBO2TORS

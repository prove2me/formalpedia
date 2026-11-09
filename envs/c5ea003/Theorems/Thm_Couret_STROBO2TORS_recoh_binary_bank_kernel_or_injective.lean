-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_binary_bank_kernel_or_injective
-- name    : Couret.STROBO2TORS.recoh_binary_bank_kernel_or_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:52.225571+00:00
-- url     : https://prove2.me/theorems/e7370d19-3d45-4888-b5f8-28e2db90cb20
-- title:
--   A binary character bank has a kernel or is injective
-- statement:
--   Let $L$ be any abelian group and $b_i:L\to\mathbb Z/2$ additive maps for $i<k$, with $k\ge0$. Then $$\exists x\ne0,\ \forall i,\ b_i(x)=0\quad\text{or}\quad(x\mapsto(b_i(x))_i)\text{ is injective}.$$ No finiteness is needed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohBinaryDichotomy.lean, lines 20–39; source file SHA-256 740733aa832d9a2d29988c8cbc79b0861bfba8e7e0e0aa8e9f9826db98ef1779; theorem Couret.STROBO2TORS.recoh_binary_bank_kernel_or_injective

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
RECOH: binary evaluation dichotomy and exact collision reduction.

This module eliminates a manual case split for arbitrary finite banks:
either a nonzero binary kernel exists or the binary evaluation is injective.
In the injective case it records the information-set selection as one
EXPLICIT hypothesis. It does not claim that selection for general rank.

The rank-one case has a separate certified branch and is not duplicated.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_binary_bank_kernel_or_injective
    {H : Type*} [AddCommGroup H]
    (k : ℕ) (binary : Fin k → H →+ ZMod 2) :
    (∃ a : H, a ≠ 0 ∧ ∀ i : Fin k, binary i a = 0) ∨
      Function.Injective (fun a : H => fun i : Fin k => binary i a) := by sorry






end Couret.STROBO2TORS

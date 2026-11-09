-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_surjective_binary_pivots_leave_short_mask
-- name    : Couret.STROBO2TORS.recoh_surjective_binary_pivots_leave_short_mask
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:36.042668+00:00
-- url     : https://prove2.me/theorems/ab697cef-6d52-4edf-a566-ad05ec6325aa
-- title:
--   Surjective pivots leave fewer than the remaining rank zero readings
-- statement:
--   Let $L$ be an abelian group, $r,s,k\ge0$ with $k<r+s$, binary additive maps $b_i:L\to\mathbb F_2$, and an injective pivot selection $p:r\hookrightarrow k$. Assume the selected map $x\mapsto(b_{p(j)}(x))_{j<r}$ is surjective. Then there exists $x\in L$ such that $$b_{p(j)}(x)=1\ (j<r),\qquad|\{i<k:b_i(x)=0\}|<s.$$ No finiteness of $L$ is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPivotMasks.lean, lines 20–79; source file SHA-256 ca749d3ade136a0a3bef0e29e0a9e22c72cc0777a775f12eb43077d9f51a1597; theorem Couret.STROBO2TORS.recoh_surjective_binary_pivots_leave_short_mask

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
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
RECOH / STROBO: binary pivot mask counting and ternary subbank kernels.

Conditional interface for the missing mixed-rank selection step.
A surjective rank-r family of binary probes lets one force r signs
simultaneously, leaving fewer than s neutral probes if k < r+s.

The UNCONDITIONAL existence of the pivot family for every full-rank
binary restriction bank is not claimed in this file.
-/

namespace Couret.STROBO2TORS

theorem recoh_surjective_binary_pivots_leave_short_mask
    {H : Type*} [AddCommGroup H]
    (r s k : ℕ) (hk : k < r + s)
    (bank : Fin k → H →+ ZMod 2)
    (pivot : Fin r → Fin k) (hpiv : Function.Injective pivot)
    (hsurj : Function.Surjective
      (fun d : H => fun j : Fin r => bank (pivot j) d)) :
    ∃ d : H, (∀ j : Fin r, bank (pivot j) d = 1) ∧
      ((Finset.univ : Finset (Fin k)).filter
        (fun i => bank i d = 0)).card < s := by sorry




end Couret.STROBO2TORS

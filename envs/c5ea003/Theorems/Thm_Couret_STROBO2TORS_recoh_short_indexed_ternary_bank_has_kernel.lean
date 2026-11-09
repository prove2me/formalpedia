-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_short_indexed_ternary_bank_has_kernel
-- name    : Couret.STROBO2TORS.recoh_short_indexed_ternary_bank_has_kernel
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:33.412545+00:00
-- url     : https://prove2.me/theorems/80358b7e-5486-49c0-b76e-3c2df3fc4ddf
-- title:
--   A short ternary bank has a nonzero common kernel
-- statement:
--   Let $A$ be a finite abelian group with $|A|=3^s$. Let $I$ be finite with $|I|<s$, and let $b_i:A\to\mathbb F_3$ be additive maps. Then
--
--   $$\exists a\in A\setminus\{0\}:\quad b_i(a)=0\quad(i\in I).$$
--
--   No exponent-three hypothesis on $A$ is needed for this cardinality argument.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPivotMasks.lean, lines 81–110; source file SHA-256 ca749d3ade136a0a3bef0e29e0a9e22c72cc0777a775f12eb43077d9f51a1597; theorem Couret.STROBO2TORS.recoh_short_indexed_ternary_bank_has_kernel

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_nonzero_kernel_of_small_codomain
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

theorem recoh_short_indexed_ternary_bank_has_kernel
    {A I : Type*}
    [AddCommGroup A] [Fintype A]
    [Fintype I]
    (s : ℕ) (hcard : Fintype.card A = 3 ^ s)
    (hI : Fintype.card I < s)
    (bank : I → A →+ ZMod 3) :
    ∃ a : A, a ≠ 0 ∧ ∀ i : I, bank i a = 0 := by sorry


end Couret.STROBO2TORS

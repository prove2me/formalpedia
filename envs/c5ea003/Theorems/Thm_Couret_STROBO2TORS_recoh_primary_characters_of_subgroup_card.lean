-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_primary_characters_of_subgroup_card
-- name    : Couret.STROBO2TORS.recoh_primary_characters_of_subgroup_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:05.218853+00:00
-- url     : https://prove2.me/theorems/d9d373e4-e7f9-4c1e-8803-761bbe434225
-- title:
--   Primary characters separate an elementary primary subgroup
-- statement:
--   Let $G$ be a finite abelian group. Let $p$ be prime and $A\le G$ have $pa=0$ for every $a\in A$, with $|A|=p^r$. There exist $r$ complex characters $\chi_i$ such that, with $v_p(|G|)$ the exponent of $p$ in $|G|$,
--
--   $$\chi_i(x)^{p^{v_p(|G|)}}=1\quad(i<r,x\in G),\qquad\bigl(\forall i<r,\chi_i(a)=1\bigr)\Longrightarrow a=0\quad(a\in A).$$
--
--   This gives primary-valued ambient measurements separating the subgroup.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPrimaryCharacters.lean, lines 108–151; source file SHA-256 aac0eb1afaa745a9c06971d4d58da34eac3567a8d188e887ea7a48d1d5932cfb; theorem Couret.STROBO2TORS.recoh_primary_characters_of_subgroup_card

import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Theorems.Thm_Couret_STROBO2TORS_recoh_complex_character_extension
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality

set_option autoImplicit false

/-!
Primary complex character banks for finite abelian groups.

The construction takes coordinates on the subgroup killed by a prime p,
extends their standard complex characters to G, then raises each extension
to the factor of |G| coprime to p.  This gives p-primary characters without
assuming that G itself has exponent p.  All existence statements below are
proved from group structure and cardinality; separation is a conclusion.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G]









variable [Fintype G]

theorem recoh_primary_characters_of_subgroup_card
    (p r : ℕ) [Fact p.Prime] (A : AddSubgroup G)
    (hpA : ∀ a : A, p • a = 0)
    (hcard : Nat.card A = p ^ r) :
    ∃ bank : Fin r → AddChar G ℂ,
      (∀ i x, (bank i x) ^ (p ^ (Fintype.card G).factorization p) = 1) ∧
      (∀ a : A, (∀ i, bank i (a : G) = 1) → a = 0) := by sorry










end Couret.STROBO2TORS

-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
-- name    : Couret.STROBO2TORS.recoh_two_primary_characters_of_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:12.651707+00:00
-- url     : https://prove2.me/theorems/3316204a-a4b3-4a2a-8e21-edaa945e721a
-- title:
--   Two-primary characters separate two-torsion
-- statement:
--   Let $G$ be a finite abelian group. If $|G[2]|=2^r$, there are $r$ complex characters $\chi_i$ such that every $\chi_i(x)$ has two-power order and they jointly separate $G[2]$:
--
--   $$\forall i,x\ \exists n\in\mathbb N:\chi_i(x)^{2^n}=1,\qquad 2x=0,\ \chi_i(x)=1\ (i<r)\Longrightarrow x=0.$$
--
--   This gives an ambient binary measurement bank of rank $r$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPrimaryCharacters.lean, lines 181–194; source file SHA-256 aac0eb1afaa745a9c06971d4d58da34eac3567a8d188e887ea7a48d1d5932cfb; theorem Couret.STROBO2TORS.recoh_two_primary_characters_of_card

import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Theorems.Thm_Couret_STROBO2TORS_recoh_primary_characters_of_subgroup_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_torsion_subgroup_nsmul
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

theorem recoh_two_primary_characters_of_card
    (r : ℕ)
    (hcard : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r) :
    ∃ bank : Fin r → AddChar G ℂ,
      (∀ i x, ∃ n : ℕ, (bank i x) ^ (2 ^ n) = 1) ∧
      (∀ x : G, x + x = 0 → (∀ i, bank i x = 1) → x = 0) := by sorry




end Couret.STROBO2TORS

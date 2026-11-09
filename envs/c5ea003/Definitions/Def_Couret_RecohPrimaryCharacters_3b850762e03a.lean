-- Prove2me | Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
-- name    : Couret_RecohPrimaryCharacters_3b850762e03a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:26.44129+00:00
-- url     : https://prove2.me/theorems/a023e733-5e96-4edf-8ab4-91d7265c8cd1
-- title:
--   Torsion subgroups and primary-character arithmetic
-- statement:
--   For an abelian group and natural $p$, define
--
--   $$G[p]=\{x\in G:px=0\}$$
--
--   as an additive subgroup. The bundle supplies the membership interface and elementary coprime-power character facts. These definitions support primary-coordinate character construction and its separation properties.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPrimaryCharacters.lean; source file SHA-256 aac0eb1afaa745a9c06971d4d58da34eac3567a8d188e887ea7a48d1d5932cfb

import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
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

/-- The subgroup of elements killed by `p`; for prime `p` this is `G[p]`. -/
def recohTorsionSubgroup (p : ℕ) : AddSubgroup G where
  carrier := {x | p • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change p • x = 0 at hx
    change p • y = 0 at hy
    change p • (x + y) = 0
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    change p • x = 0 at hx
    change p • (-x) = 0
    rw [smul_neg, hx, neg_zero]

@[simp]
theorem recoh_mem_torsion_subgroup (p : ℕ) (x : G) :
    x ∈ recohTorsionSubgroup (G := G) p ↔ p • x = 0 := Iff.rfl





variable [Fintype G]



/-- Coprime powers can both equal one only at one. -/
theorem recoh_eq_one_of_coprime_powers
    {M : Type*} [Monoid M] (z : M) (p q : ℕ)
    (hpq : Nat.Coprime p q) (hp : z ^ p = 1) (hq : z ^ q = 1) :
    z = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [← hpq.gcd_eq_one]
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp)
    (orderOf_dvd_of_pow_eq_one hq)







omit [Fintype G] in
/-- A `p`-primary complex character vanishes on torsion of order coprime
to `p`, in the multiplicative sense of having value one. -/
theorem recoh_primary_character_trivial_of_coprime
    (p q n : ℕ) (hpq : Nat.Coprime p q) (χ : AddChar G ℂ)
    (hprimary : ∀ x, (χ x) ^ (p ^ n) = 1)
    (x : G) (hx : q • x = 0) : χ x = 1 := by
  apply recoh_eq_one_of_coprime_powers (χ x) (p ^ n) q
    (hpq.pow_left n) (hprimary x)
  rw [← χ.map_nsmul_eq_pow, hx, χ.map_zero_eq_one]





end Couret.STROBO2TORS



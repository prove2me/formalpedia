-- Prove2me | Definitions.Def_Kourovka_Collection_Collection
-- name    : Kourovka_Collection_Collection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:43:22.53062+00:00
-- url     : https://prove2.me/theorems/6ab38a00-0136-42a2-aa66-88e977a411e7
-- title:
--   Collection
-- statement:
--   Definitions and structural lemmas for Collection, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
def raise {k : ℕ} (v : Lattice k) (i : Fin k) : Lattice k :=
  Function.update v i (v i + 1)
def Solid {k : ℕ} (B : Set (Lattice k)) : Prop :=
  ∀ v w, w ∈ B → (∀ i, |v i| ≤ |w i|) → v ∈ B
def prefixBudget {k : ℕ} (B : Set (Lattice (k + 1))) : Set (Lattice k) :=
  {v | Fin.snoc v 0 ∈ B}
def lower {k : ℕ} (v : Lattice k) (i : Fin k) : Lattice k :=
  Function.update v i (v i - 1)
def OrderedOrbit {a k : ℕ} (A : Fin a → G) (t : Fin k → G) : Set G :=
  {x | ∃ p v, x = conjugate (A p) (orderedWord t v)}
end Kourovka.MetabelianEnumeration.FiniteCover.Collection



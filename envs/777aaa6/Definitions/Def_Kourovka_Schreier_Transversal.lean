-- Prove2me | Definitions.Def_Kourovka_Schreier_Transversal
-- name    : Kourovka_Schreier_Transversal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:39:42.866512+00:00
-- url     : https://prove2.me/theorems/0cc69982-e54c-418d-9c51-ca6a6db4e6c4
-- title:
--   Transversal
-- statement:
--   Definitions and structural lemmas for Transversal, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
set_option autoImplicit true
namespace Kourovka.Schreier
variable {X : Type*}
structure Transversal (L : Subgroup (FreeGroup X)) where
  rep : FreeGroup X → FreeGroup X
  sameCoset : ∀ w, w * (rep w)⁻¹ ∈ L
  constantOnCosets : ∀ {u v}, u * v⁻¹ ∈ L → rep u = rep v
  rep_one : rep 1 = 1
namespace Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
def vertices : Set (FreeGroup X) := Set.range S.rep
abbrev Edge := S.vertices × X
def edge (p : FreeGroup X) (x : X) : S.Edge := (⟨S.rep p, ⟨p, rfl⟩⟩, x)
def edgeValue (z : S.Edge) : FreeGroup X :=
  z.1.val * FreeGroup.of z.2 * (S.rep (z.1.val * FreeGroup.of z.2))⁻¹
theorem edgeValue_mem (z : S.Edge) : S.edgeValue z ∈ L :=
  S.sameCoset (z.1.val * FreeGroup.of z.2)
def evaluate : FreeGroup S.Edge →* L :=
  FreeGroup.lift (fun z => ⟨S.edgeValue z, S.edgeValue_mem z⟩)
end Transversal
end Kourovka.Schreier



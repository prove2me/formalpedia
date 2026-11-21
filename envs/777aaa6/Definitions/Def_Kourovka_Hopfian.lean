-- Prove2me | Definitions.Def_Kourovka_Hopfian
-- name    : Kourovka_Hopfian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:27:45.853353+00:00
-- url     : https://prove2.me/theorems/56115b47-0c4e-45e4-b371-250cbe47f012
-- title:
--   Hopfian
-- statement:
--   Definitions and structural lemmas for Hopfian, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Hopfian.lean

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Card
set_option autoImplicit true
namespace Kourovka
def IsHopfian (G : Type*) [Group G] : Prop :=
  ∀ f : G →* G, Function.Surjective f → Function.Injective f
variable {G H : Type*} [Group G] [Group H]
end Kourovka



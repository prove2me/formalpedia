-- Prove2me | solution 1 for Kourovka.subsingleton_of_solvable_perfect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:51.189955+00:00
-- url     : https://prove2.me/submissions/7b1ad4ef-7439-45ee-85f3-84779e25245b

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Card
import Definitions.Def_Kourovka_Hopfian

set_option autoImplicit true
open Kourovka
variable {G H : Type*} [Group G] [Group H]
namespace Kourovka
theorem _root_.solution [IsSolvable G]
    (h : commutator G = ⊤) : Subsingleton G := by
  by_contra hn
  letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hn
  exact (ne_of_lt (IsSolvable.commutator_lt_top_of_nontrivial G)) h
end Kourovka

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.realizationHom_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:53.906901+00:00
-- url     : https://prove2.me/submissions/20fbe692-b407-47f8-a87c-688cd75f0449

import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Definitions.Def_Kourovka_Covers_FiniteCover

set_option autoImplicit true
attribute [-instance] instConditionallyCompleteLinearOrder
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A) (i : Fin (k + a)) :
    realizationHom data radius t A h (PresentedGroup.of i) = generatorAssignment t A i :=
  PresentedGroup.toGroup.of _
end Kourovka.MetabelianEnumeration.FiniteCover

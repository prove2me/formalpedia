-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.relators_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:51.382195+00:00
-- url     : https://prove2.me/submissions/50e80317-783f-46b4-9710-893c98e23913

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
theorem _root_.solution {k a : ℕ} (data : Datum k a) (radius : ℕ) :
    (WordCertificates.relSet (relators data radius)).Finite := List.finite_toSet _
end Kourovka.MetabelianEnumeration.FiniteCover

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.map_filter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:58.96815+00:00
-- url     : https://prove2.me/submissions/c64507cc-0b95-4cf3-9b9f-2eb638aaf4d3

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution {α β : Type*} (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (l : List α) :
    (l.filter p).map f = (l.map f).filter q := by
  induction l with
  | nil => rfl
  | cons x l ih => cases hpx : p x <;> simp [h, hpx, ih]
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin

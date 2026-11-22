-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.casesOn_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:45:24.427302+00:00
-- url     : https://prove2.me/submissions/9852e149-bba5-4574-9540-3d14fda0e637

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a)) :=
  (Primrec.sumCasesOn ((Primrec.of_equiv (e := Equiv.intEquivNatSumNat)).comp hf) hg hh).of_eq
    (fun a => by cases f a <;> rfl)
end Kourovka.MetabelianEnumeration.ComputableIntegers

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.expand_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:04.891921+00:00
-- url     : https://prove2.me/submissions/c74a556a-2fbc-4edc-8a4e-e267840e58b8

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit [DecidableEq G]
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution : Primrec₂ (@expand G _) := by
  have hi : Primrec (fun p : List G × List G => p.2.map Inv.inv) :=
    Primrec.list_map Primrec.snd (hinv.comp Primrec.snd).to₂
  have hm : Primrec (fun p : List G × List G =>
      p.2.flatMap fun x => p.2.map fun y => x * y) :=
    Primrec.list_flatMap Primrec.snd
      (Primrec.list_map (Primrec.snd.comp Primrec.fst)
        (hmul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  have hc : Primrec (fun p : List G × List G =>
      p.1.flatMap fun g => p.2.map fun x => g * x * g⁻¹) :=
    Primrec.list_flatMap Primrec.fst
      (Primrec.list_map (Primrec.snd.comp Primrec.fst)
        (hmul.comp (hmul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
          (hinv.comp (Primrec.snd.comp Primrec.fst))).to₂).to₂
  exact Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp Primrec.snd hi) hm) hc
end Kourovka.MetabelianEnumeration.ComputableClosure

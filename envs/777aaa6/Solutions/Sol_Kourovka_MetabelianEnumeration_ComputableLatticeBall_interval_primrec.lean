-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableLatticeBall.interval_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:29.745386+00:00
-- url     : https://prove2.me/submissions/7e329482-9217-4009-8544-4e8fe4e5440b

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_ofNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_sub_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableLatticeBall
theorem _root_.solution : Primrec interval := by
  have hf : Primrec (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ)) :=
    ComputableIntegers.sub_primrec.comp (ofNat_primrec.comp Primrec.snd)
      (ofNat_primrec.comp Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))) hf.to₂
end Kourovka.MetabelianEnumeration.ComputableLatticeBall

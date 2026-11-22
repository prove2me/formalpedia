-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.Derivation.eval_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:50:32.857746+00:00
-- url     : https://prove2.me/submissions/4bba0d8e-2d5f-4f0d-8879-d347d6864c4a

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
namespace Derivation
theorem _root_.solution {n : ℕ} (rels : List (FreeGroup (Fin n)))
    (d : Derivation n) : d.eval rels ∈ Subgroup.normalClosure {r | r ∈ rels} := by
  induction d with
  | one => exact Subgroup.one_mem _
  | relator w =>
    simp only [Derivation.eval]
    split
    · exact Subgroup.subset_normalClosure (by assumption)
    · exact Subgroup.one_mem _
  | mul l r hl hr => exact Subgroup.mul_mem _ hl hr
  | inv d hd => exact Subgroup.inv_mem _ hd
  | conjugate w d hd => exact Subgroup.Normal.conj_mem inferInstance _ hd _
end Derivation
end Kourovka.MetabelianEnumeration.WordCertificates

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.lowerBound_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:50:11.036065+00:00
-- url     : https://prove2.me/submissions/d4d62c80-3e94-4490-bfad-246dcf225f48

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) {p q : GroupRing Q} {c d : ℝ}
    (hp : LowerBound χ p c) (hq : LowerBound χ q d) : LowerBound χ (p * q) (c + d) := by
  intro u hu
  obtain ⟨v, hv, w, hw, rfl⟩ := Finset.mem_image₂.mp (AddMonoidAlgebra.support_mul p q hu)
  simpa using add_le_add (hp v hv) (hq w hw)
end Kourovka.MetabelianEnumeration.ValuationModule

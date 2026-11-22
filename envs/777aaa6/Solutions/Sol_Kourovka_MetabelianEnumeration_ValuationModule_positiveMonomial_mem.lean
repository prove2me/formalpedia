-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.positiveMonomial_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:47.684452+00:00
-- url     : https://prove2.me/submissions/94eb7c35-0187-4b4d-88c4-e8f2137e2f89

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (q : Q) (hq : 0 < χ q) :
    positiveMonomial χ q hq ∈ positiveIdeal χ := by
  intro u hu
  have : u = q := by simpa [positiveMonomial, AddMonoidAlgebra.single_apply, eq_comm] using hu
  exact this.symm ▸ hq
end Kourovka.MetabelianEnumeration.ValuationModule

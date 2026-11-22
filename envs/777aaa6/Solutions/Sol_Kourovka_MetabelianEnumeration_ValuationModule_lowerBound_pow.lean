-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.lowerBound_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:52.22375+00:00
-- url     : https://prove2.me/submissions/c3d89fb5-b5a3-4add-98d5-d5616ba4159a

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_lowerBound_mul

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) {p : GroupRing Q} {c : ℝ}
    (hp : LowerBound χ p c) (n : ℕ) : LowerBound χ (p ^ n) (n * c) := by
  induction n with
  | zero =>
    intro u hu
    have : u = 0 := by simpa [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply, eq_comm] using hu
    simp [this]
  | succ n ih =>
    simpa [pow_succ, Nat.cast_add, add_mul] using lowerBound_mul χ ih hp
end Kourovka.MetabelianEnumeration.ValuationModule

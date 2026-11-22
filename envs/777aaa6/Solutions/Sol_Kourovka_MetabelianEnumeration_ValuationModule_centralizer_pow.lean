-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.centralizer_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:05.042223+00:00
-- url     : https://prove2.me/submissions/304b4c18-521d-468e-90d1-a9cf567f48d4

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
omit [DecidableEq Q]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution {p : GroupRing Q} (hp : ∀ m : M, p • m = m) (n : ℕ) :
    ∀ m : M, (p ^ n) • m = m := by
  induction n with
  | zero => simp
  | succ n ih => intro m; rw [pow_succ, mul_smul, hp, ih]
end Kourovka.MetabelianEnumeration.ValuationModule

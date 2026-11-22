-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
-- name    : Kourovka_Halfspaces_HalfspaceModule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:55.60495+00:00
-- url     : https://prove2.me/theorems/41bb4ed7-5365-4314-a062-beff0c231d9d
-- title:
--   Halfspace Module
-- statement:
--   Definitions and structural lemmas for Halfspace Module, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean

import Definitions.Def_Kourovka_Modules_ValuationModule
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
noncomputable def monomial (q : Q) : GroupRing Q := AddMonoidAlgebra.single q 1
noncomputable def shift (q : Q) (m : M) : M := monomial q • m
omit [DecidableEq Q] in
@[simp] theorem monomial_zero : monomial (0 : Q) = 1 := by
  simp [monomial, ← AddMonoidAlgebra.one_def]
omit [DecidableEq Q] in
@[simp] theorem shift_zero (m : M) : shift (0 : Q) m = m := by simp [shift]
omit [DecidableEq Q] in
@[simp] theorem shift_add (q : Q) (m n : M) : shift q (m + n) = shift q m + shift q n :=
  smul_add _ _ _
omit [DecidableEq Q] in
@[simp] theorem shift_sub (q : Q) (m n : M) : shift q (m - n) = shift q m - shift q n :=
  smul_sub _ _ _
noncomputable def halfMonomial (χ : Q →+ ℝ) (q : Q) (hq : 0 ≤ χ q) : nonnegativeRing χ :=
  ⟨monomial q, by
    intro v hv
    have hvq : v = q := by
      simpa [monomial, AddMonoidAlgebra.single_apply, eq_comm] using hv
    simpa only [hvq] using hq⟩
end Kourovka.MetabelianEnumeration.HalfspaceModule



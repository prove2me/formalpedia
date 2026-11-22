-- Prove2me | Definitions.Def_Kourovka_Modules_SignedTameness
-- name    : Kourovka_Modules_SignedTameness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:50.030399+00:00
-- url     : https://prove2.me/theorems/b7449091-cceb-46b1-baae-f0a8cff1ee9c
-- title:
--   Signed Tameness
-- statement:
--   Definitions and structural lemmas for Signed Tameness, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/SignedTameness.lean

import Definitions.Def_Kourovka_Modules_ValuationModule
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.SignedTameness
open FiniteCover ConeVerifier ValuationModule TamenessCompactness
def character {k : ℕ} (x : Fin k → ℝ) : Lattice k →+ ℝ where
  toFun u := ∑ i, x i * (u i : ℝ)
  map_zero' := by simp
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
abbrev SignedPolynomial (k : ℕ) := Bool × GroupRing (Lattice k)
def signedSupport {k : ℕ} (p : SignedPolynomial k) : List (Vec k) :=
  p.2.support.toList.map fun u => fun i => if p.1 then (u i : ℚ) else -(u i : ℚ)
variable {k : ℕ} {M : Type*} [AddCommGroup M] [Module (GroupRing (Lattice k)) M]
def Tame (M : Type*) [AddCommGroup M] [Module (GroupRing (Lattice k)) M] : Prop :=
  ∀ x : Fin k → ℝ, x ≠ 0 →
    Module.Finite (nonnegativeRing (character x)) M ∨
    Module.Finite (nonnegativeRing (-character x)) M
end Kourovka.MetabelianEnumeration.SignedTameness



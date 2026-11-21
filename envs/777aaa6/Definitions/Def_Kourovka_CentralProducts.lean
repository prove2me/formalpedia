-- Prove2me | Definitions.Def_Kourovka_CentralProducts
-- name    : Kourovka_CentralProducts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:30:30.165718+00:00
-- url     : https://prove2.me/theorems/0f4694a7-8d89-41e4-a84f-ae5bc19f378a
-- title:
--   Central Products
-- statement:
--   Definitions and structural lemmas for Central Products, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralProducts.lean

import Definitions.Def_Kourovka_Components
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Theorems.Thm_Kourovka_ProductHom_left_center
import Theorems.Thm_Kourovka_ProductHom_right_center

set_option autoImplicit true
namespace Kourovka
namespace CentralProducts
variable {G : Type*} [Group G] (P Q : Subgroup G)
    (hc : ∀ p : P, ∀ q : Q, Commute (p : G) (q : G))
def multiply : P × Q →* G := P.subtype.noncommCoprod Q.subtype hc
@[simp] theorem multiply_apply (p : P) (q : Q) : multiply P Q hc (p, q) = p * q := rfl
theorem multiply_surjective (hcover : ∀ g : G, ∃ p : P, ∃ q : Q, (p : G) * q = g) :
    Function.Surjective (multiply P Q hc) := by
  intro g
  obtain ⟨p, q, h⟩ := hcover g
  exact ⟨(p, q), h⟩
variable (hcover : ∀ g : G, ∃ p : P, ∃ q : Q, (p : G) * q = g)
include P Q hc hcover in
theorem left_center {p : P} (hp : p ∈ Subgroup.center P) :
    (p : G) ∈ Subgroup.center G := by
  simpa only [ProductHom.left_apply, multiply_apply, OneMemClass.coe_one, mul_one] using
    ProductHom.left_center (multiply P Q hc) (multiply_surjective P Q hc hcover) hp
include P Q hc hcover in
theorem right_center {q : Q} (hq : q ∈ Subgroup.center Q) :
    (q : G) ∈ Subgroup.center G := by
  simpa only [ProductHom.right_apply, multiply_apply, OneMemClass.coe_one, one_mul] using
    ProductHom.right_center (multiply P Q hc) (multiply_surjective P Q hc hcover) hq
include hc in
/-- A central product element has central components in their own factors. -/
theorem components_central {p : P} {q : Q}
    (hpq : (p : G) * q ∈ Subgroup.center G) :
    p ∈ Subgroup.center P ∧ q ∈ Subgroup.center Q := by
  have hh := Subgroup.mem_center_iff.mp hpq
  constructor
  · rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    change (a : G) * p = p * a
    apply mul_right_cancel (b := (q : G))
    calc
      ((a : G) * p) * q = a * ((p : G) * q) := mul_assoc _ _ _
      _ = ((p : G) * q) * a := hh a
      _ = (p : G) * ((q : G) * a) := mul_assoc _ _ _
      _ = (p : G) * ((a : G) * q) := by rw [(hc a q).eq]
      _ = ((p : G) * a) * q := (mul_assoc _ _ _).symm
  · rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    change (b : G) * q = q * b
    apply mul_left_cancel (a := (p : G))
    calc
      (p : G) * ((b : G) * q) = ((p : G) * b) * q := (mul_assoc _ _ _).symm
      _ = ((b : G) * p) * q := by rw [(hc p b).eq]
      _ = (b : G) * ((p : G) * q) := mul_assoc _ _ _
      _ = ((p : G) * q) * b := hh b
      _ = (p : G) * ((q : G) * b) := mul_assoc _ _ _
def leftQuotient : P ⧸ Subgroup.center P →* G ⧸ Subgroup.center G :=
  QuotientGroup.map (Subgroup.center P) (Subgroup.center G) P.subtype
    (fun _ hp => left_center P Q hc hcover hp)
def rightQuotient : Q ⧸ Subgroup.center Q →* G ⧸ Subgroup.center G :=
  QuotientGroup.map (Subgroup.center Q) (Subgroup.center G) Q.subtype
    (fun _ hq => right_center P Q hc hcover hq)
theorem quotient_commute (p : P ⧸ Subgroup.center P) (q : Q ⧸ Subgroup.center Q) :
    Commute (leftQuotient P Q hc hcover p) (rightQuotient P Q hc hcover q) := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  exact (hc p q).map (QuotientGroup.mk' (Subgroup.center G))
def quotientMultiply : (P ⧸ Subgroup.center P) × (Q ⧸ Subgroup.center Q) →*
    G ⧸ Subgroup.center G :=
  (leftQuotient P Q hc hcover).noncommCoprod (rightQuotient P Q hc hcover)
    (quotient_commute P Q hc hcover)
theorem quotientMultiply_bijective : Function.Bijective (quotientMultiply P Q hc hcover) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    rintro ⟨p, q⟩ hpq
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
    have h : (p : G) * q ∈ Subgroup.center G := by
      change (QuotientGroup.mk' (Subgroup.center G)) (p : G) *
        (QuotientGroup.mk' (Subgroup.center G)) (q : G) = 1 at hpq
      rw [← map_mul] at hpq
      exact (QuotientGroup.eq_one_iff _).mp hpq
    obtain ⟨hp, hq⟩ := components_central P Q hc h
    exact Prod.ext ((QuotientGroup.eq_one_iff _).mpr hp) ((QuotientGroup.eq_one_iff _).mpr hq)
  · intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨p, q, rfl⟩ := hcover g
    exact ⟨(QuotientGroup.mk p, QuotientGroup.mk q),
      ((QuotientGroup.mk' (Subgroup.center G)).map_mul (p : G) (q : G)).symm⟩
noncomputable def quotientEquiv :
    (P ⧸ Subgroup.center P) × (Q ⧸ Subgroup.center Q) ≃* G ⧸ Subgroup.center G :=
  MulEquiv.ofBijective (quotientMultiply P Q hc hcover) (quotientMultiply_bijective P Q hc hcover)
end CentralProducts
variable {G : Type*} [Group G]
end Kourovka



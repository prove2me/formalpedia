-- Prove2me | Definitions.Def_Kourovka_CenterQuotients
-- name    : Kourovka_CenterQuotients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:31:28.147075+00:00
-- url     : https://prove2.me/theorems/87038b13-d317-46bf-8d62-834c8a4aed4d
-- title:
--   Center Quotients
-- statement:
--   Definitions and structural lemmas for Center Quotients, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterQuotients.lean

import Definitions.Def_Kourovka_CenterWeight
set_option autoImplicit true
namespace Kourovka
namespace CenterQuotients
variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]
theorem center_product_iff (a : A) (b : B) :
    (a, b) ∈ Subgroup.center (A × B) ↔ a ∈ Subgroup.center A ∧ b ∈ Subgroup.center B := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h
    exact ⟨fun x => congrArg Prod.fst (h (x, 1)),
      fun y => congrArg Prod.snd (h (1, y))⟩
  · rintro ⟨ha, hb⟩ ⟨x, y⟩
    exact Prod.ext (ha x) (hb y)
theorem map_center (f : G →* H) (hf : Function.Surjective f)
    {z : G} (hz : z ∈ Subgroup.center G) : f z ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
def quotientMap (f : G →* H) (hf : Function.Surjective f) :
    G ⧸ Subgroup.center G →* H ⧸ Subgroup.center H :=
  QuotientGroup.map _ _ f (fun _ hz => map_center f hf hz)
def quotientInl : A ⧸ Subgroup.center A →* (A × B) ⧸ Subgroup.center (A × B) :=
  QuotientGroup.map _ _ (MonoidHom.inl A B)
    (fun _ ha => (center_product_iff _ _).mpr ⟨ha, (Subgroup.center B).one_mem⟩)
def quotientInr : B ⧸ Subgroup.center B →* (A × B) ⧸ Subgroup.center (A × B) :=
  QuotientGroup.map _ _ (MonoidHom.inr A B)
    (fun _ hb => (center_product_iff _ _).mpr ⟨(Subgroup.center A).one_mem, hb⟩)
theorem quotientInl_commute_quotientInr (a : A ⧸ Subgroup.center A)
    (b : B ⧸ Subgroup.center B) : Commute (quotientInl a) (quotientInr b) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply Commute.map _ (QuotientGroup.mk' (Subgroup.center (A × B)))
  change (a, (1 : B)) * ((1 : A), b) = (1, b) * (a, 1)
  simp
def quotientProduct : (A ⧸ Subgroup.center A) × (B ⧸ Subgroup.center B) →*
    (A × B) ⧸ Subgroup.center (A × B) :=
  quotientInl.noncommCoprod quotientInr quotientInl_commute_quotientInr
@[simp] theorem quotientProduct_mk (a : A) (b : B) :
    quotientProduct (QuotientGroup.mk a, QuotientGroup.mk b) = QuotientGroup.mk (a, b) := by
  change (QuotientGroup.mk' (Subgroup.center (A × B))) (a, 1) *
    (QuotientGroup.mk' (Subgroup.center (A × B))) (1, b) = _
  rw [← map_mul]
  simp
theorem quotientProduct_bijective : Function.Bijective (quotientProduct (A := A) (B := B)) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    rintro ⟨a, b⟩ hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    change quotientProduct (QuotientGroup.mk a, QuotientGroup.mk b) = 1 at hab
    rw [quotientProduct_mk] at hab
    obtain ⟨ha, hb⟩ := (center_product_iff a b).mp ((QuotientGroup.eq_one_iff _).mp hab)
    exact Prod.ext ((QuotientGroup.eq_one_iff _).mpr ha) ((QuotientGroup.eq_one_iff _).mpr hb)
  · intro z
    obtain ⟨⟨a, b⟩, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨(QuotientGroup.mk a, QuotientGroup.mk b), quotientProduct_mk a b⟩
noncomputable def productEquiv :
    (A ⧸ Subgroup.center A) × (B ⧸ Subgroup.center B) ≃*
      (A × B) ⧸ Subgroup.center (A × B) :=
  MulEquiv.ofBijective quotientProduct quotientProduct_bijective
end CenterQuotients
end Kourovka



-- Prove2me | solution 1 for mme_CW_q6_primaryHashFamily_uniform_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:40:53.121283+00:00
-- url     : https://prove2.me/submissions/bedf1e61-764b-4faf-a596-c34d4497011a

import Mathlib.Tactic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

set_option autoImplicit false
set_option warningAsError true

/-- Select uniformly many retained entries from selected outer fibers of a
primary hash family.  All structural hash-family properties and any
pointwise address predicate are inherited. -/
theorem solution
    {N L G A H H' : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (P : Finset (Fin A × Fin H)) (outer : Finset (Fin A))
    (Good : CWQ6ExactCoupledAddress N L G → Prop)
    (hH' : 0 < H') (hHle : H' ≤ H)
    (hfiber : ∀ a ∈ outer,
      H' ≤ (P.filter (fun p ↦ p.1 = a)).card)
    (hGood : ∀ p ∈ P, Good (family.entry p)) :
    ∃ subfamily : CWQ6PrimaryHashFamily N L G outer.card H',
      (∀ p, Good (subfamily.entry p)) ∧ H' ≤ H := by
  classical
  let outerEnum : Fin outer.card ≃ ↥outer := outer.equivFin.symm
  let fiber (a : Fin outer.card) : Finset (Fin A × Fin H) :=
    P.filter (fun p ↦ p.1 = (outerEnum a).1)
  have hfiberLower (a : Fin outer.card) : H' ≤ (fiber a).card := by
    exact hfiber (outerEnum a).1 (outerEnum a).2
  let chosen (a : Fin outer.card) : Finset (Fin A × Fin H) :=
    Classical.choose ((fiber a).exists_subset_card_eq (hfiberLower a))
  have hchosen (a : Fin outer.card) :
      chosen a ⊆ fiber a ∧ (chosen a).card = H' := by
    exact Classical.choose_spec
      ((fiber a).exists_subset_card_eq (hfiberLower a))
  let edgeEnum (a : Fin outer.card) : Fin H' ≃ ↥(chosen a) :=
    (Finset.equivFinOfCardEq (hchosen a).2).symm
  let selected (p : Fin outer.card × Fin H') : Fin A × Fin H :=
    (edgeEnum p.1 p.2).1
  have hselectedMem (p : Fin outer.card × Fin H') : selected p ∈ P := by
    exact (Finset.mem_filter.mp
      ((hchosen p.1).1 (edgeEnum p.1 p.2).2)).1
  have hselectedFirst (p : Fin outer.card × Fin H') :
      (selected p).1 = (outerEnum p.1).1 := by
    exact (Finset.mem_filter.mp
      ((hchosen p.1).1 (edgeEnum p.1 p.2).2)).2
  have hselectedInjective : Function.Injective selected := by
    rintro ⟨a, h⟩ ⟨b, k⟩ heq
    have hab : a = b := by
      apply outerEnum.injective
      apply Subtype.ext
      calc
        (outerEnum a).1 = (selected (a, h)).1 :=
          (hselectedFirst (a, h)).symm
        _ = (selected (b, k)).1 := congrArg Prod.fst heq
        _ = (outerEnum b).1 := hselectedFirst (b, k)
    subst b
    have hhk : h = k := by
      apply (edgeEnum a).injective
      apply Subtype.ext
      exact heq
    subst k
    rfl
  let entry (p : Fin outer.card × Fin H') :
      CWQ6ExactCoupledAddress N L G := family.entry (selected p)
  have hxInjective : Function.Injective (fun p ↦ (entry p).1 0) := by
    intro p q h
    exact hselectedInjective (family.xInjective h)
  have hyInjective : Function.Injective (fun p ↦ (entry p).1 1) := by
    intro p q h
    exact hselectedInjective (family.yInjective h)
  have hzSame : ∀ (a : Fin outer.card) (h k : Fin H'),
      (entry (a, h)).1 2 = (entry (a, k)).1 2 := by
    intro a h k
    have eh : selected (a, h) =
        ((outerEnum a).1, (selected (a, h)).2) :=
      Prod.ext (hselectedFirst (a, h)) rfl
    have ek : selected (a, k) =
        ((outerEnum a).1, (selected (a, k)).2) :=
      Prod.ext (hselectedFirst (a, k)) rfl
    change (family.entry (selected (a, h))).1 2 =
      (family.entry (selected (a, k))).1 2
    rw [eh, ek]
    exact family.zSameFiber _ _ _
  have hzSeparate : ∀ (a b : Fin outer.card) (h k : Fin H'),
      (entry (a, h)).1 2 = (entry (b, k)).1 2 → a = b := by
    intro a b h k hz
    have hzOuter : (selected (a, h)).1 = (selected (b, k)).1 := by
      apply family.zSeparatesFibers
      simpa only [entry] using hz
    apply outerEnum.injective
    apply Subtype.ext
    calc
      (outerEnum a).1 = (selected (a, h)).1 :=
        (hselectedFirst (a, h)).symm
      _ = (selected (b, k)).1 := hzOuter
      _ = (outerEnum b).1 := hselectedFirst (b, k)
  have hinduced : ∀ p q r : Fin outer.card × Fin H',
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress (entry p).1 (entry q).1 (entry r).1) →
      p = q ∧ p.1 = r.1 := by
    intro p q r hsupp
    have hold := family.induced (selected p) (selected q) (selected r)
      (by simpa only [entry] using hsupp)
    refine ⟨hselectedInjective hold.1, ?_⟩
    apply outerEnum.injective
    apply Subtype.ext
    calc
      (outerEnum p.1).1 = (selected p).1 :=
        (hselectedFirst p).symm
      _ = (selected r).1 := hold.2
      _ = (outerEnum r.1).1 := hselectedFirst r
  let subfamily : CWQ6PrimaryHashFamily N L G outer.card H' := {
    hHpos := hH'
    entry := entry
    xInjective := hxInjective
    yInjective := hyInjective
    zSameFiber := hzSame
    zSeparatesFibers := hzSeparate
    induced := hinduced
  }
  refine ⟨subfamily, ?_, hHle⟩
  intro p
  exact hGood (selected p) (hselectedMem p)

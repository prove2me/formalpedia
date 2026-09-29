-- Prove2me | solution 1 for mme_dwz_table2_component_words_supply_outer_layout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T15:22:35.560747+00:00
-- url     : https://prove2.me/submissions/2c2497de-38f1-4de3-9b33-37eb6aeb5abf

import Definitions.Def_mme_dwz_table2_split_assignments

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZTable2ComponentWordLayout

open MME.DWZTable2Cardinality

private abbrev TaggedPosition (m : ℕ) :=
  Σ r : SplitRegion, RegionPosition m r

private def regionOfShape (s : Fin 15) : SplitRegion :=
  if h : MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

private theorem coarseDegree_regionOfShape (s : Fin 15) :
    coarseDegree (regionOfShape s) = MME.DWZSquare.shapeZ s := by
  simp only [regionOfShape]
  split <;> rfl

private theorem region_component_pushforward (r : SplitRegion) :
    (∑ s : {s : Fin 15 // regionOfShape s = r},
      MME.DWZTable2Counts.component s.1) = regionSize 1 r := by
  classical
  fin_cases r <;> decide

private def groupedShapeFiberEquiv
    {Position : Type*} (shapeWord : Position → Fin 15)
    (r : SplitRegion) :
    (Σ s : {s : Fin 15 // regionOfShape s = r},
      {t : Position // shapeWord t = s.1}) ≃
      {t : Position // regionOfShape (shapeWord t) = r} where
  toFun x := ⟨x.2.1, by rw [x.2.2, x.1.2]⟩
  invFun t := ⟨⟨shapeWord t.1, t.2⟩, ⟨t.1, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    cases ht
    rfl
  right_inv t := by cases t; rfl

private theorem component_word_region_card
    {m : ℕ} {Position : Type*} [Fintype Position]
    (shapeWord : Position → Fin 15)
    (hshape : ∀ s,
      Fintype.card {t : Position // shapeWord t = s} =
        MME.DWZTable2Counts.component s * m)
    (r : SplitRegion) :
    Fintype.card {t : Position // regionOfShape (shapeWord t) = r} =
      regionSize m r := by
  rw [← Fintype.card_congr (groupedShapeFiberEquiv shapeWord r),
    Fintype.card_sigma]
  simp_rw [hshape]
  rw [← Finset.sum_mul, region_component_pushforward]
  cases r <;> simp [regionSize]

private noncomputable def regionFiberEquiv
    {m : ℕ} {Position : Type*} [Fintype Position]
    (shapeWord : Position → Fin 15)
    (hshape : ∀ s,
      Fintype.card {t : Position // shapeWord t = s} =
        MME.DWZTable2Counts.component s * m)
    (r : SplitRegion) :
    RegionPosition m r ≃
      {t : Position // regionOfShape (shapeWord t) = r} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,
      component_word_region_card shapeWord hshape r])

private noncomputable def componentWordLayout
    {m : ℕ} {Position : Type*} [Fintype Position]
    (shapeWord : Position → Fin 15)
    (hshape : ∀ s,
      Fintype.card {t : Position // shapeWord t = s} =
        MME.DWZTable2Counts.component s * m) :
    TaggedPosition m ≃ Position :=
  (Equiv.sigmaCongrRight (regionFiberEquiv shapeWord hshape)).trans
    (Equiv.sigmaFiberEquiv (fun t ↦ regionOfShape (shapeWord t)))

private theorem componentWordLayout_region
    {m : ℕ} {Position : Type*} [Fintype Position]
    (shapeWord : Position → Fin 15)
    (hshape : ∀ s,
      Fintype.card {t : Position // shapeWord t = s} =
        MME.DWZTable2Counts.component s * m)
    (x : TaggedPosition m) :
    regionOfShape (shapeWord (componentWordLayout shapeWord hshape x)) = x.1 := by
  simp only [componentWordLayout, Equiv.trans_apply,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
  exact (regionFiberEquiv shapeWord hshape x.1 x.2).2

end MME.DWZTable2ComponentWordLayout

open MME.DWZTable2Cardinality
open MME.DWZTable2ComponentWordLayout

theorem solution
    (m : ℕ)
    {Outer Position : Type*}
    [Finite Outer] [Fintype Position]
    (K : Position → Fin 5)
    (shapeWord : Outer → Position → Fin 15)
    (hshape : ∀ (I : Outer) (s : Fin 15),
      Fintype.card {t : Position // shapeWord I t = s} =
        MME.DWZTable2Counts.component s * m)
    (hmatch : ∀ (I : Outer) (t : Position),
      MME.DWZSquare.shapeZ (shapeWord I t) = K t) :
    ∃ layout : ∀ _I : Outer,
        (Σ r : SplitRegion, RegionPosition m r) ≃ Position,
      ∀ (I : Outer) (x : Σ r : SplitRegion, RegionPosition m r),
        K (layout I x) = coarseDegree x.1 := by
  classical
  let layout : ∀ _I : Outer,
      (Σ r : SplitRegion, RegionPosition m r) ≃ Position :=
    fun I ↦ componentWordLayout (shapeWord I) (hshape I)
  refine ⟨layout, ?_⟩
  intro I x
  calc
    K (layout I x) = MME.DWZSquare.shapeZ (shapeWord I (layout I x)) :=
      (hmatch I (layout I x)).symm
    _ = coarseDegree (regionOfShape (shapeWord I (layout I x))) :=
      (coarseDegree_regionOfShape _).symm
    _ = coarseDegree x.1 := by
      rw [componentWordLayout_region]

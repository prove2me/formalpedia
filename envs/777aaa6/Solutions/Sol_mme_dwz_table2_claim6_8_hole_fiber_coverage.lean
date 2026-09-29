-- Prove2me | solution 1 for mme_dwz_table2_claim6_8_hole_fiber_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T20:40:38.415077+00:00
-- url     : https://prove2.me/submissions/e802f2d9-52ae-418d-b139-ca26b6f7d33f

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (b0 : ZMod p) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let n := sourceLength - 1
    let reindex : Fin (n + 1) ≃ Fin sourceLength :=
      finCongr (by
        dsimp only [n, sourceLength]
        exact Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Outer :=
      {w : Fin sourceLength → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Fin sourceLength // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Typical :=
      {small : Fin sourceLength → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ q, Fintype.card {t : Fin sourceLength // small t = q} =
          MME.DWZTable2Counts.gamma q * m}
    let Compatible : Outer → Typical → Prop := fun I small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Fin sourceLength //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
      MME.DWZSquare.shapeX (I.1 (reindex t))
    let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
    ∀ (retained : Outer) (small : Typical),
      Compatible retained small →
      let outerCandidates :=
        Finset.univ.filter
          (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
      let hX : (Fin (n + 1) → ZMod p) →
          (Fin (n + 1) → Fin 5) → ZMod p :=
        fun w A ↦ b0 + ∑ t, ((A t).val : ZMod p) * w t
      let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
          (Fin (n + 1) → Fin 5) → ZMod p :=
        fun w0 w C ↦
          b0 + (2 : ZMod p)⁻¹ *
            (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)
      let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
        fun w ↦
          2 * (∑ t, ((addressX retained t).val : ZMod p) * w t) -
            ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
      let hashCompatibleFiber :
          (Fin (n + 1) → ZMod p) → Finset Outer := fun w ↦
        Finset.univ.filter (fun A : Outer ↦
          Compatible A small ∧
            hX w (addressX A) = hZ (conditionedW0 w) w addressZ)
      let bad : (Fin (n + 1) → ZMod p) → Prop := fun w ↦
        1 < (hashCompatibleFiber w).card
      ∀ w, bad w →
        ∃ A ∈ outerCandidates,
          hX w (addressX A) = hZ (conditionedW0 w) w addressZ := by
  classical
  dsimp only
  intro retained small hretained w hhole
  let sourceLength := MME.DWZTable2Counts.scale * m
  let n := sourceLength - 1
  have hsourceLength : n + 1 = sourceLength := by
    dsimp only [n, sourceLength]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm)))
  let reindex : Fin (n + 1) ≃ Fin sourceLength := finCongr hsourceLength
  let regionOfShape :
      Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
    if h : MME.DWZSquare.shapeX s = 0 ∨
        MME.DWZSquare.shapeY s = 0 then
      Sum.inl ⟨s, h⟩
    else
      Sum.inr (MME.DWZSquare.shapeZ s)
  let Outer :=
    {word : Fin sourceLength → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (word t) = K t) ∧
      ∀ s, Fintype.card {t : Fin sourceLength // word t = s} =
        MME.DWZTable2Counts.component s * m}
  let compatible : Outer → Prop := fun I ↦
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Fin sourceLength //
            regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m r a
  let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
    MME.DWZSquare.shapeX (I.1 (reindex t))
  let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
  let outerCandidates : Finset Outer :=
    Finset.univ.filter (fun A ↦ A ≠ retained ∧ compatible A)
  let hX : (Fin (n + 1) → ZMod p) →
      (Fin (n + 1) → Fin 5) → ZMod p :=
    fun weights A ↦ b0 + ∑ t, ((A t).val : ZMod p) * weights t
  let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
      (Fin (n + 1) → Fin 5) → ZMod p :=
    fun w0 weights C ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * weights t)
  let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
    fun weights ↦
      2 * (∑ t, ((addressX retained t).val : ZMod p) * weights t) -
        ∑ t, ((4 : ZMod p) - (addressZ t).val) * weights t
  let fiber : Finset Outer :=
    Finset.univ.filter (fun A ↦ compatible A ∧
      hX w (addressX A) = hZ (conditionedW0 w) w addressZ)
  change compatible retained at hretained
  change 1 < fiber.card at hhole
  change ∃ A ∈ outerCandidates,
    hX w (addressX A) = hZ (conditionedW0 w) w addressZ
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have htwo : (2 : ZMod p)⁻¹ * 2 = 1 :=
    ZMod.inv_mul_of_unit 2 hunit
  have hcollisionRetained :
      hX w (addressX retained) = hZ (conditionedW0 w) w addressZ := by
    simp only [hX, hZ, conditionedW0]
    rw [sub_add_cancel]
    calc
      b0 + ∑ t, ((addressX retained t).val : ZMod p) * w t =
          b0 + 1 * (∑ t,
            ((addressX retained t).val : ZMod p) * w t) := by ring
      _ = b0 + ((2 : ZMod p)⁻¹ * 2) *
          (∑ t, ((addressX retained t).val : ZMod p) * w t) := by
            rw [htwo]
      _ = b0 + (2 : ZMod p)⁻¹ *
          (2 * (∑ t,
            ((addressX retained t).val : ZMod p) * w t)) := by ring
  have hretainedMem : retained ∈ fiber := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ retained, hretained, hcollisionRetained⟩
  have hErasePos : 0 < (fiber.erase retained).card := by
    have hcard := Finset.card_erase_of_mem hretainedMem
    omega
  obtain ⟨A, hAErase⟩ := Finset.card_pos.mp hErasePos
  have hAData := Finset.mem_erase.mp hAErase
  have hAMem := Finset.mem_filter.mp hAData.2
  refine ⟨A, ?_, hAMem.2.2⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ A, hAData.1, hAMem.2.1⟩

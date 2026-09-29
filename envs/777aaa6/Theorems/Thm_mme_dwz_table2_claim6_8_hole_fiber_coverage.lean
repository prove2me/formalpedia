-- Prove2me | Theorems.Thm_mme_dwz_table2_claim6_8_hole_fiber_coverage
-- name    : mme_dwz_table2_claim6_8_hole_fiber_coverage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T20:40:02.892731+00:00
-- url     : https://prove2.me/theorems/9962214f-c919-400b-9c2b-a9c7d5756c1d
-- title:
--   DWZ Table 2 Claim 6.8: finite collision-fiber coverage
-- statement:
--   Fix a positive Table-2 multiplier, a coarse Z word, a retained exact Table-2 outer word, and a typical small word compatible with it. For each conditioned hash-weight word, form the finite fiber of all compatible outer words over that same coarse Z word whose X hash equals the retained conditioned Z hash. If this fiber has more than one element, then there is an element distinct from the retained word in the exact compatible candidate family, and it satisfies the collision premise required by the bounded-address Claim-6.8 adapter. This is the finite collision-incidence implication only; it does not identify tensor support or an actual zeroed block with the fiber-cardinality event.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.2: Definition 6.1, Claim 6.2, Additional Zeroing-Out Step 2, and Claim 6.8.

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_claim6_8_hole_fiber_coverage
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
          hX w (addressX A) = hZ (conditionedW0 w) w addressZ := by sorry

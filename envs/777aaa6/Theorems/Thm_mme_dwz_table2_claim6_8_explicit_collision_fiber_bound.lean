-- Prove2me | Theorems.Thm_mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
-- name    : mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T20:49:20.840341+00:00
-- url     : https://prove2.me/theorems/a172d67a-79ec-4a58-9fb1-26ab18def99f
-- title:
--   DWZ Table 2 Claim 6.8: explicit compatible collision-fiber one-eighth bound
-- statement:
--   Fix a positive Table-2 multiplier, a coarse Z word, an odd prime p > 4, and the affine hash offset. Over the exact fixed-Z Table-2 outer family and exact typical fine words, fix a retained outer word compatible with a typical word. Let the alternative candidate family consist literally of the other compatible outer words. For each conditioned hash-weight word, let the compatible hash fiber consist of all compatible outer words whose X hash equals the retained conditioned Z hash. If 8 times the number of alternative candidates is at most p, then 8 times the number of weight words for which this fiber has cardinality greater than one is at most the cardinality of the full finite weight space. This is the finite hashing core of Claim 6.8; it does not identify the fiber event with an actual tensor-support hole.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.2, especially Additional Zeroing-Out Step 2 and Claim 6.8, together with the conditioned affine hashing machinery of Section 3; https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_table2_claim6_8_bounded_address_adapter
import Theorems.Thm_mme_dwz_table2_claim6_8_hole_fiber_coverage

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hlevel : 4 < p) (b0 : ZMod p) :
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
      8 * outerCandidates.card ≤ p →
        8 * (Finset.univ.filter bad).card ≤
          Fintype.card (Fin (n + 1) → ZMod p) := by
  sorry

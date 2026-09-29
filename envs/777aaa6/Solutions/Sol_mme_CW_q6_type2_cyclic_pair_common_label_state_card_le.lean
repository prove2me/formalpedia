-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_pair_common_label_state_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:05:26.814114+00:00
-- url     : https://prove2.me/submissions/105380c8-f7e4-4a3e-9fa1-6cff771a6dc2

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_mode_word_tuple_injective
import Theorems.Thm_mme_CW_q6_type2_cyclic_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_difference_normal_form
import Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e f : CWQ6Type2CyclicEdge N L G) (S : Finset (ZMod p))
    (hne : e ≠ f) (shared : Fin 3)
    (hshared : cwQ6Type2CyclicModeWord e shared =
      cwQ6Type2CyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3) (a : CWQ6Type2CyclicEdge N L G) ↦
      cwQ6Type2CyclicAffineHash p N L G
        (weights q.1, (6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : CWQ6Type2CyclicEdge N L G) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
    ((Finset.univ.filter (fun q ↦ retain q e ∧ retain q f)).card) ≤
      p ^ (6 * N) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let H := fun (q : (I → ZMod p) × ZMod p)
      (i : Fin 3) (a : CWQ6Type2CyclicEdge N L G) ↦
    cwQ6Type2CyclicAffineHash p N L G
      (weights q.1, (6 : ZMod p)⁻¹ * q.2) i a
  let retain := fun (q : (I → ZMod p) × ZMod p)
      (a : CWQ6Type2CyclicEdge N L G) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
  let joint : ((I → ZMod p) × ZMod p) → Prop := fun q ↦
    retain q e ∧ retain q f
  change ((Finset.univ.filter joint).card) ≤ _
  have hcard : Fintype.card I = 6 * N + 1 := by
    simp [I]
    omega
  have hmodeNe : cwQ6Type2CyclicModeWord e ≠
      cwQ6Type2CyclicModeWord f := by
    intro h
    exact hne (mme_CW_q6_type2_cyclic_mode_word_tuple_injective h)
  obtain ⟨k, hk⟩ : ∃ k : Fin 3,
      cwQ6Type2CyclicModeWord e k ≠
        cwQ6Type2CyclicModeWord f k := by
    by_contra h
    push_neg at h
    exact hmodeNe (funext h)
  obtain ⟨r, j, hpivot⟩ :=
    mme_CW_q6_type2_cyclic_distinct_mode_code_difference_has_nonzero_coefficient
      hp e f k hk
  let c : I → ZMod p
    | Sum.inl x =>
        cwQ6Type2CyclicHashModeCode p N k
            (cwQ6Type2CyclicModeWord e k) x.1 x.2 -
          cwQ6Type2CyclicHashModeCode p N k
            (cwQ6Type2CyclicModeWord f k) x.1 x.2
    | Sum.inr _ => 0
  have hc : c (Sum.inl (r, j)) ≠ 0 := by
    simpa [c] using hpivot
  let L0 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N 0
        (cwQ6Type2CyclicModeWord e 0) r j * w (Sum.inl (r, j))
  let L2 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cwQ6Type2CyclicHashModeCode p N 2
        (cwQ6Type2CyclicModeWord e 2) r j * w (Sum.inl (r, j))
  let offset : (I → ZMod p) → ZMod p := fun w ↦ L0 w - L2 w
  have h6 : (6 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 6 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hH0 (q : (I → ZMod p) × ZMod p) : H q 0 e = L0 q.1 := by
    simpa [H, weights, L0] using
      (mme_CW_q6_type2_cyclic_affine_hash_normal_form
        (p := p) (N := N) (L := L) (G := G)
        (weights q.1, (6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 e = q.2 + L2 q.1 := by
    rw [show H q 2 e =
        6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, L2] using
        (mme_CW_q6_type2_cyclic_affine_hash_normal_form
          (p := p) (N := N) (L := L) (G := G)
          (weights q.1, (6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hvertex (q : (I → ZMod p) × ZMod p)
      (a b : CWQ6Type2CyclicEdge N L G) (i : Fin 3)
      (hab : cwQ6Type2CyclicModeWord a i =
        cwQ6Type2CyclicModeWord b i) :
      H q i a = H q i b := by
    dsimp only [H]
    rw [mme_CW_q6_type2_cyclic_affine_hash_normal_form
      (weights q.1, (6 : ZMod p)⁻¹ * q.2) i a]
    rw [mme_CW_q6_type2_cyclic_affine_hash_normal_form
      (weights q.1, (6 : ZMod p)⁻¹ * q.2) i b]
    rw [hab]
  have hcsum (w : I → ZMod p) :
      (∑ x : I, c x * w x) =
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          (cwQ6Type2CyclicHashModeCode p N k
                (cwQ6Type2CyclicModeWord e k) r j -
              cwQ6Type2CyclicHashModeCode p N k
                (cwQ6Type2CyclicModeWord f k) r j) *
            w (Sum.inl (r, j)) := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [I, c]
  have hnormal (q : (I → ZMod p) × ZMod p)
      (hq : joint q) :
      (∑ x : I, c x * q.1 x) = 0 ∧ q.2 = offset q.1 := by
    rcases hq with ⟨⟨se, _hse, he⟩, ⟨sf, _hsf, hf⟩⟩
    have hlabel : se = sf := by
      have hv := hvertex q e f shared hshared
      rw [he shared, hf shared] at hv
      exact hv
    have hkhash : H q k e = H q k f := by
      exact (he k).trans (hlabel.trans (hf k).symm)
    constructor
    · rw [hcsum q.1]
      rw [← mme_CW_q6_type2_cyclic_affine_hash_difference_normal_form
        (weights q.1, (6 : ZMod p)⁻¹ * q.2) k e f]
      exact sub_eq_zero.mpr hkhash
    · have he20 : H q 2 e = H q 0 e :=
        (he 2).trans (he 0).symm
      rw [hH2 q, hH0 q] at he20
      dsimp only [offset]
      linear_combination he20
  exact mme_ZMod_prime_affine_joint_fintype_card_le
    hcard c (Sum.inl (r, j)) hc offset joint hnormal

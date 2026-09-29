-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_pair_retention_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:09:29.021378+00:00
-- url     : https://prove2.me/submissions/656d6ced-8dba-41f7-9090-3fe4b8494f5b

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_mode_word_tuple_injective
import Theorems.Thm_mme_stothers_phi233_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_difference_normal_form
import Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le

open BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e f : CyclicAmbientEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) (hne : e ≠ f) (shared : Fin 3)
    (hshared : cyclicModeWord e shared = cyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3) (a : CyclicAmbientEdge N alpha beta gamma delta) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : CyclicAmbientEdge N alpha beta gamma delta) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
    ((Finset.univ.filter (fun q ↦ retain q e ∧ retain q f)).card) ≤
      p ^ (6 * N) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
  let H := fun (q : (I → ZMod p) × ZMod p)
      (i : Fin 3) (a : CyclicAmbientEdge N alpha beta gamma delta) ↦
    cyclicAffineHash p N alpha beta gamma delta
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
  let retain := fun (q : (I → ZMod p) × ZMod p)
      (a : CyclicAmbientEdge N alpha beta gamma delta) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
  let joint : ((I → ZMod p) × ZMod p) → Prop := fun q ↦
    retain q e ∧ retain q f
  change ((Finset.univ.filter joint).card) ≤ _
  have hcard : Fintype.card I = 6 * N + 1 := by
    simp [I]
    omega
  have hmodeNe : cyclicModeWord e ≠ cyclicModeWord f := by
    intro h
    exact hne (mme_stothers_phi233_cyclic_mode_word_tuple_injective h)
  obtain ⟨k, hk⟩ : ∃ k : Fin 3,
      cyclicModeWord e k ≠ cyclicModeWord f k := by
    by_contra h
    push_neg at h
    exact hmodeNe (funext h)
  obtain ⟨r, j, hpivot⟩ :=
    mme_stothers_phi233_distinct_mode_code_difference_has_nonzero_coefficient
      (by omega : 5 ≤ p) e f k hk
  let c : I → ZMod p
    | Sum.inl x =>
        cyclicHashModeCode p N k (cyclicModeWord e k) x.1 x.2 -
          cyclicHashModeCode p N k (cyclicModeWord f k) x.1 x.2
    | Sum.inr _ => 0
  have hc : c (Sum.inl (r, j)) ≠ 0 := by
    simpa [c] using hpivot
  let L0 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 0 (cyclicModeWord e 0) r j *
        w (Sum.inl (r, j))
  let L2 : (I → ZMod p) → ZMod p := fun w ↦
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N 2 (cyclicModeWord e 2) r j *
        w (Sum.inl (r, j))
  let offset : (I → ZMod p) → ZMod p := fun w ↦ L0 w - L2 w
  have h6 : (6 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 6 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hH0 (q : (I → ZMod p) × ZMod p) :
      H q 0 e = shift q.1 + L0 q.1 := by
    simpa [H, weights, shift, L0] using
      (mme_stothers_phi233_cyclic_affine_hash_normal_form
        (p := p) (N := N) (alpha := alpha) (beta := beta)
        (gamma := gamma) (delta := delta)
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 0 e)
  have hH2 (q : (I → ZMod p) × ZMod p) :
      H q 2 e = shift q.1 + q.2 + L2 q.1 := by
    rw [show H q 2 e =
        shift q.1 + 6 * ((6 : ZMod p)⁻¹ * q.2) + L2 q.1 by
      simpa [H, weights, shift, L2] using
        (mme_stothers_phi233_cyclic_affine_hash_normal_form
          (p := p) (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta)
          (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) 2 e)]
    rw [← mul_assoc, mul_inv_cancel₀ h6, one_mul]
  have hvertex (q : (I → ZMod p) × ZMod p)
      (a b : CyclicAmbientEdge N alpha beta gamma delta) (i : Fin 3)
      (hab : cyclicModeWord a i = cyclicModeWord b i) :
      H q i a = H q i b := by
    dsimp only [H]
    rw [mme_stothers_phi233_cyclic_affine_hash_normal_form
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a]
    rw [mme_stothers_phi233_cyclic_affine_hash_normal_form
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i b]
    rw [hab]
  have hcsum (w : I → ZMod p) :
      (∑ x : I, c x * w x) =
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          (cyclicHashModeCode p N k (cyclicModeWord e k) r j -
            cyclicHashModeCode p N k (cyclicModeWord f k) r j) *
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
      rw [← mme_stothers_phi233_cyclic_affine_hash_difference_normal_form
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) k e f]
      exact sub_eq_zero.mpr hkhash
    · have he20 : H q 2 e = H q 0 e :=
        (he 2).trans (he 0).symm
      rw [hH2 q, hH0 q] at he20
      dsimp only [offset]
      linear_combination he20
  exact mme_ZMod_prime_affine_joint_fintype_card_le
    hcard c (Sum.inl (r, j)) hc offset joint hnormal

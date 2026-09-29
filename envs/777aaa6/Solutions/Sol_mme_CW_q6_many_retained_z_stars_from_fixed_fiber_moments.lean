-- Prove2me | solution 1 for mme_CW_q6_many_retained_z_stars_from_fixed_fiber_moments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:18:15.945471+00:00
-- url     : https://prove2.me/submissions/5dfa5742-029e-4aec-ba52-de021f14a29e

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_many_weights_above_half_mean
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem card_product_filter_eq_sum
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (W : Finset α) (B : Finset β)
    (P : α → β → Prop) [DecidableRel P] :
    ((W.product B).filter (fun p => P p.1 p.2)).card =
      ∑ w ∈ W, (B.filter (fun b => P w b)).card := by
  simp only [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  calc
    (∑ a ∈ W.product B, if P a.1 a.2 then 1 else 0) =
        ∑ w ∈ W, ∑ b ∈ B, if P w b then 1 else 0 := by
      exact Finset.sum_product W B
        (fun p => if P p.1 p.2 then 1 else 0)
    _ = ∑ w ∈ W, ∑ b ∈ B with P w b, 1 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_filter]

private theorem finite_bipartite_cross_averaging
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (hV : V.Nonempty)
    (P : α → β → Prop) [DecidableRel P]
    (A C : ℕ)
    (hleft : ∀ a ∈ U,
      A ≤ C * (V.filter (fun b => P a b)).card) :
    ∃ b ∈ V,
      A * U.card ≤
        C * V.card * (U.filter (fun a => P a b)).card := by
  let total : ℕ := ∑ a ∈ U, (V.filter (fun b => P a b)).card
  have hsum : A * U.card ≤ C * total := by
    calc
      A * U.card = ∑ _a ∈ U, A := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ U, C * (V.filter (fun b => P a b)).card := by
        exact Finset.sum_le_sum hleft
      _ = C * total := by
        simp only [total, Finset.mul_sum]
  have hdouble : total =
      ∑ b ∈ V, (U.filter (fun a => P a b)).card := by
    simpa only [total] using
      (mme_finset_incidence_double_count U V (fun a b => P a b))
  have havg : ∃ b ∈ V,
      total ≤ V.card * (U.filter (fun a => P a b)).card := by
    apply Finset.exists_le_of_sum_le hV
    rw [show (∑ _b ∈ V, total) = V.card * total by simp]
    rw [← Finset.mul_sum]
    rw [← hdouble]
  obtain ⟨b, hb, hbavg⟩ := havg
  refine ⟨b, hb, hsum.trans ?_⟩
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left C hbavg

/-- Uniform fixed-Z moments and exact offset multiplicity aggregate to one
affine parameter retaining many Z-stars at the common degree threshold. -/
theorem solution
    {M n L G B H : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (Z : Finset (Fin (2 * (n + 1)) → Fin 3))
    (A : (Fin (2 * (n + 1)) → Fin 3) →
      Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (hz : ∀ z ∈ Z, ∀ e ∈ A z, e.1 2 = z)
    (hcard : ∀ z ∈ Z, (A z).card = B)
    (hB : 0 < B) (hH : 2 * M * H ≤ B)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M) :
    let degree :
        (Fin (2 * (n + 1)) → Fin 3) →
          (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
      ((A z).attach.filter (fun e =>
        ∑ i,
          ((2 * ((e.1.1 0 i).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
    ∃ w : Fin (2 * n + 2) → ZMod M,
      ∃ b0 : ZMod M,
        B * S.card * Z.card ≤
          4 * M * (2 * M + B) *
            (Z.filter (fun z =>
              H ≤ degree z w ∧
                ∃ s ∈ S,
                  cwQ6DoubledZHash b0 w z =
                    2 * (s : ZMod M))).card := by
  classical
  let degree :
      (Fin (2 * (n + 1)) → Fin 3) →
        (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
    ((A z).attach.filter (fun e =>
      ∑ i,
        ((2 * ((e.1.1 0 i).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
  let W : Finset (Fin (2 * n + 2) → ZMod M) := Finset.univ
  let O : Finset (ZMod M) := Finset.univ
  let Ω : Finset ((Fin (2 * n + 2) → ZMod M) × ZMod M) := W.product O
  let P : (Fin (2 * (n + 1)) → Fin 3) →
      ((Fin (2 * n + 2) → ZMod M) × ZMod M) → Prop := fun z q =>
    H ≤ degree z q.1 ∧
      ∃ s ∈ S,
        cwQ6DoubledZHash q.2 q.1 z = 2 * (s : ZMod M)
  have hWcard : W.card = M ^ (2 * n + 2) := by
    simp [W]
  have hOcard : O.card = M := by
    simp [O]
  have hΩcard : Ω.card = M ^ (2 * n + 2) * M := by
    simp [Ω, hWcard, hOcard]
  have hΩnonempty : Ω.Nonempty := by
    simp [Ω, W, O]
  have hperZ : ∀ z ∈ Z,
      B * M ^ (2 * n + 2) * S.card ≤
        (4 * (2 * M + B)) * (Ω.filter (fun q => P z q)).card := by
    intro z hzZ
    have hpz := mme_CW_q6_fixed_z_many_weights_above_half_mean
      hM h2 hG (A z) z (hz z hzZ) (hcard z hzZ) hB hH
    change
      (B : ℝ) * (M : ℝ) ^ (2 * n + 2) ≤
        4 * (2 * (M : ℝ) + (B : ℝ)) *
          (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
            (fun w => H ≤ degree z w)).card : ℝ) at hpz
    have hpzNat :
        B * M ^ (2 * n + 2) ≤
          4 * (2 * M + B) *
            (W.filter (fun w => H ≤ degree z w)).card := by
      exact_mod_cast hpz
    have hpair :
        (Ω.filter (fun q => P z q)).card =
          (W.filter (fun w => H ≤ degree z w)).card * S.card := by
      calc
        (Ω.filter (fun q => P z q)).card =
            ∑ w ∈ W, (O.filter (fun b0 => P z (w, b0))).card := by
          simpa only [Ω] using
            card_product_filter_eq_sum W O (fun w b0 => P z (w, b0))
        _ = ∑ w ∈ W,
              if H ≤ degree z w then S.card else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hgood : H ≤ degree z w
          · have hoff := mme_CW_q6_z_hash_offset_label_card
                h2 S hSrange w z
            simp only [P, hgood, true_and, O] at hoff ⊢
            exact hoff
          · simp [P, hgood]
        _ = (W.filter (fun w => H ≤ degree z w)).card * S.card := by
          rw [← Finset.sum_filter]
          simp
    rw [hpair]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_right S.card hpzNat
  obtain ⟨q, hqΩ, hq⟩ := finite_bipartite_cross_averaging
    Z Ω hΩnonempty P (B * M ^ (2 * n + 2) * S.card)
      (4 * (2 * M + B)) hperZ
  have hWpos : 0 < M ^ (2 * n + 2) := by
    positivity
  refine ⟨q.1, q.2, ?_⟩
  have hcancel :
      (B * S.card * Z.card) * M ^ (2 * n + 2) ≤
        (4 * M * (2 * M + B) *
          (Z.filter (fun z => P z q)).card) * M ^ (2 * n + 2) := by
    rw [hΩcard] at hq
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq
  have hfinal := Nat.le_of_mul_le_mul_right hcancel hWpos
  simpa only [P, degree] using hfinal

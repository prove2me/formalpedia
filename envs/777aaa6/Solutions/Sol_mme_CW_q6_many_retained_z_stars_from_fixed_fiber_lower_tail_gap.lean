-- Prove2me | solution 1 for mme_CW_q6_many_retained_z_stars_from_fixed_fiber_lower_tail_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:56:03.878773+00:00
-- url     : https://prove2.me/submissions/392da90a-f32c-4b1f-8522-7a5e6846b1b5

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem card_product_filter_eq_sum_gap
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

private theorem finite_bipartite_cross_averaging_with_error
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (hV : V.Nonempty)
    (P : α → β → Prop) [DecidableRel P]
    (A C E : ℕ)
    (hleft : ∀ a ∈ U,
      A ≤ C * (V.filter (fun b => P a b)).card + E) :
    ∃ b ∈ V,
      A * U.card ≤
        C * V.card * (U.filter (fun a => P a b)).card + E * U.card := by
  let total : ℕ := ∑ a ∈ U, (V.filter (fun b => P a b)).card
  have hsum : A * U.card ≤ C * total + E * U.card := by
    calc
      A * U.card = ∑ _a ∈ U, A := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ U,
          (C * (V.filter (fun b => P a b)).card + E) := by
        exact Finset.sum_le_sum hleft
      _ = C * total + E * U.card := by
        simp only [total, Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        simp [Nat.mul_comm]
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
  have hmul := Nat.mul_le_mul_left C hbavg
  have hadd := Nat.add_le_add_right hmul (E * U.card)
  simpa [Nat.mul_assoc] using hadd

/-- The arbitrary-gap fixed-Z lower tail estimate and exact compatible-offset
count aggregate to one common affine parameter.  This counts literal shared
Z-stars only; it does not assert X/Y isolation or a tensor restriction. -/
theorem solution
    {M n L G B H R : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (Z : Finset (Fin (2 * (n + 1)) → Fin 3))
    (A : (Fin (2 * (n + 1)) → Fin 3) →
      Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (hz : ∀ z ∈ Z, ∀ e ∈ A z, e.1 2 = z)
    (hcard : ∀ z ∈ Z, (A z).card = B)
    (hgap : M * H + R ≤ B)
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
        R ^ 2 * S.card * Z.card ≤
          R ^ 2 * M *
              (Z.filter (fun z =>
                H ≤ degree z w ∧
                  ∃ s ∈ S,
                    cwQ6DoubledZHash b0 w z =
                      2 * (s : ZMod M))).card +
            2 * B * M * S.card * Z.card := by
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
  have hΩcard : Ω.card = M ^ (2 * n + 3) := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ]
    simp [Ω, hWcard, hOcard]
  have hΩnonempty : Ω.Nonempty := by
    simp [Ω, W, O]
  have hperZ : ∀ z ∈ Z,
      R ^ 2 * M ^ (2 * n + 2) * S.card ≤
        R ^ 2 * (Ω.filter (fun q => P z q)).card +
          2 * B * M ^ (2 * n + 3) * S.card := by
    intro z hzZ
    have htail := mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
      hM h2 hG (A z) z
      (hz z hzZ) (hcard z hzZ) hgap
    change
      R ^ 2 * (W.filter (fun w => ¬ H ≤ degree z w)).card ≤
        2 * B * M ^ (2 * n + 3) at htail
    have hpair :
        (Ω.filter (fun q => P z q)).card =
          (W.filter (fun w => H ≤ degree z w)).card * S.card := by
      calc
        (Ω.filter (fun q => P z q)).card =
            ∑ w ∈ W, (O.filter (fun b0 => P z (w, b0))).card := by
          simpa only [Ω] using
            card_product_filter_eq_sum_gap W O (fun w b0 => P z (w, b0))
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
    have hpartition :
        (W.filter (fun w => H ≤ degree z w)).card +
            (W.filter (fun w => ¬ H ≤ degree z w)).card = W.card := by
      exact W.card_filter_add_card_filter_not (fun w => H ≤ degree z w)
    have hraw :
        R ^ 2 * W.card * S.card ≤
          R ^ 2 *
              (W.filter (fun w => H ≤ degree z w)).card * S.card +
            2 * B * M ^ (2 * n + 3) * S.card := by
      calc
        R ^ 2 * W.card * S.card =
            R ^ 2 *
                ((W.filter (fun w => H ≤ degree z w)).card +
                  (W.filter (fun w => ¬ H ≤ degree z w)).card) * S.card := by
              rw [hpartition]
        _ = R ^ 2 *
                (W.filter (fun w => H ≤ degree z w)).card * S.card +
              (R ^ 2 *
                (W.filter (fun w => ¬ H ≤ degree z w)).card) * S.card := by
              ring
        _ ≤ R ^ 2 *
                (W.filter (fun w => H ≤ degree z w)).card * S.card +
              (2 * B * M ^ (2 * n + 3)) * S.card := by
              exact Nat.add_le_add_left
                (Nat.mul_le_mul_right S.card htail) _
    rw [hWcard] at hraw
    rw [hpair]
    simpa [Nat.mul_assoc] using hraw
  obtain ⟨q, hqΩ, hq⟩ := finite_bipartite_cross_averaging_with_error
    Z Ω hΩnonempty P
      (R ^ 2 * M ^ (2 * n + 2) * S.card) (R ^ 2)
      (2 * B * M ^ (2 * n + 3) * S.card) hperZ
  refine ⟨q.1, q.2, ?_⟩
  have hpow : M ^ (2 * n + 3) = M ^ (2 * n + 2) * M := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ]
  have hpowerPos : 0 < M ^ (2 * n + 2) := by
    positivity
  have hcancel :
      (R ^ 2 * S.card * Z.card) * M ^ (2 * n + 2) ≤
        (R ^ 2 * M * (Z.filter (fun z => P z q)).card +
          2 * B * M * S.card * Z.card) * M ^ (2 * n + 2) := by
    rw [hΩcard, hpow] at hq
    convert hq using 1 <;> ring
  have hfinal := Nat.le_of_mul_le_mul_right hcancel hpowerPos
  simpa only [P, degree] using hfinal


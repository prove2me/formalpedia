-- Prove2me | solution 1 for bernoulli_finite_coordinate_intersection_probability_from_pointwise_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T19:47:06.716798+00:00
-- url     : https://prove2.me/submissions/01229725-c71c-42ea-afa4-506044ccea6d

import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma bernoulliEventProb_true
    {n₁ n₂ : ℕ} (p : ℝ) :
    bernoulliEventProb p (fun _ : Finset (Fin n₁ × Fin n₂) => True) = 1 := by
  unfold bernoulliEventProb
  simpa using (bernoulliObservationWeight_sum_eq_one (n₁ := n₁) (n₂ := n₂) (p := p))

private theorem finite_coordinate_intersection_aux
    {n₁ n₂ : ℕ} (p c failureScale : ℝ)
    (Event : (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop)
    (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hPoint :
      ∀ w : Fin n₁ × Fin n₂,
        bernoulliEventProb p (Event w) ≥ 1 - c * failureScale) :
    ∀ s : Finset (Fin n₁ × Fin n₂),
      bernoulliEventProb p
          (fun Omega => ∀ w : Fin n₁ × Fin n₂, w ∈ s → Event w Omega) ≥
        1 - (((s.card : ℝ) * c) * failureScale) := by
  intro s
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bernoulliEventProb_true]
  | insert a s ha ih =>
      have hA :
          bernoulliEventProb p (Event a) ≥ 1 - c * failureScale :=
        hPoint a
      have hB :
          bernoulliEventProb p
              (fun Omega =>
                ∀ w : Fin n₁ × Fin n₂, w ∈ s → Event w Omega) ≥
            1 - ((s.card : ℝ) * c) * failureScale :=
        ih
      have hInter :=
        bernoulli_event_intersection_probability_from_lower_bounds
          p c ((s.card : ℝ) * c) failureScale
          (Event a)
          (fun Omega =>
            ∀ w : Fin n₁ × Fin n₂, w ∈ s → Event w Omega)
          hp hp_one hA hB
      have hcard : (insert a s).card = s.card + 1 := by
        simp [ha]
      have hconst :
          (c + (s.card : ℝ) * c) * failureScale =
            (((insert a s).card : ℝ) * c) * failureScale := by
        rw [hcard, Nat.cast_add, Nat.cast_one]
        ring
      have hevent :
          (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              Event a Omega ∧
                (∀ w : Fin n₁ × Fin n₂, w ∈ s → Event w Omega)) =
            (fun Omega =>
              ∀ w : Fin n₁ × Fin n₂, w ∈ insert a s → Event w Omega) := by
        funext Omega
        apply propext
        constructor
        · intro h w hw
          rcases h with ⟨haEvent, hsEvent⟩
          by_cases hwa : w = a
          · simpa [hwa] using haEvent
          · exact hsEvent w (by simpa [Finset.mem_insert, hwa] using hw)
        · intro h
          constructor
          · exact h a (by simp)
          · intro w hw
            exact h w (by simp [hw])
      simpa [hevent, hconst] using hInter

theorem solution
    {n₁ n₂ : ℕ} (p c failureScale : ℝ)
    (Event : (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ w : Fin n₁ × Fin n₂,
      bernoulliEventProb p (Event w) ≥ 1 - c * failureScale) →
    bernoulliEventProb p (fun Omega => ∀ w : Fin n₁ × Fin n₂, Event w Omega) ≥
      1 - (((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * c) * failureScale) := by
  intro hp hp_one hPoint
  have h :=
    finite_coordinate_intersection_aux p c failureScale Event hp hp_one hPoint
      (Finset.univ : Finset (Fin n₁ × Fin n₂))
  simpa using h

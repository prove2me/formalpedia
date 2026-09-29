-- Prove2me | solution 1 for bernoulli_four_event_intersection_probability_from_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:18:52.062051+00:00
-- url     : https://prove2.me/submissions/0da598a2-9ff6-46a1-b5a5-3143064646bf

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open scoped Classical BigOperators
open Finset

private theorem bern_total {n₁ n₂ : ℕ} (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  unfold bernoulliObservationWeight
  rw [← Finset.powerset_univ]
  have key := Finset.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1:ℝ) - p) Finset.univ
  have hL : ∏ _i : Fin n₁ × Fin n₂, (p + (1 - p)) = 1 := by
    rw [Finset.prod_const, Finset.card_univ]
    have h1 : p + (1 - p) = 1 := by ring
    rw [h1, one_pow]
  simp only [] at key
  rw [hL] at key
  refine Eq.trans ?_ key.symm
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const, Finset.prod_const]
  rw [show (univ \ t).card = Fintype.card (Fin n₁ × Fin n₂) - t.card from by
        rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]]

private theorem inter2 {n₁ n₂ : ℕ} (p cA cB failureScale : ℝ)
    (EventA EventB : Finset (Fin n₁ × Fin n₂) → Prop)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : bernoulliEventProb p EventA ≥ 1 - cA * failureScale)
    (hB : bernoulliEventProb p EventB ≥ 1 - cB * failureScale) :
    bernoulliEventProb p (fun Omega => EventA Omega ∧ EventB Omega) ≥
      1 - (cA + cB) * failureScale := by
  have hw : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  have key : bernoulliEventProb p EventA + bernoulliEventProb p EventB
              - bernoulliEventProb p (fun Omega => EventA Omega ∧ EventB Omega) ≤ 1 := by
    rw [← bern_total (n₁ := n₁) (n₂ := n₂) p]
    unfold bernoulliEventProb
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro Omega _
    have hwO := hw Omega
    by_cases hA' : EventA Omega
    · by_cases hB' : EventB Omega
      · simp only [if_pos hA', if_pos hB', if_pos (And.intro hA' hB')]; linarith
      · have hn : ¬ (EventA Omega ∧ EventB Omega) := fun h => hB' h.2
        simp only [if_pos hA', if_neg hB', if_neg hn]; linarith
    · have hn : ¬ (EventA Omega ∧ EventB Omega) := fun h => hA' h.1
      by_cases hB' : EventB Omega
      · simp only [if_neg hA', if_pos hB', if_neg hn]; linarith
      · simp only [if_neg hA', if_neg hB', if_neg hn]; linarith
  have hexp : (cA + cB) * failureScale = cA * failureScale + cB * failureScale := by ring
  linarith [key, hA, hB, hexp]

theorem solution
    {n₁ n₂ : ℕ} (p cA cB cC cD failureScale : ℝ)
    (EventA EventB EventC EventD : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p EventA ≥ 1 - cA * failureScale →
    bernoulliEventProb p EventB ≥ 1 - cB * failureScale →
    bernoulliEventProb p EventC ≥ 1 - cC * failureScale →
    bernoulliEventProb p EventD ≥ 1 - cD * failureScale →
    bernoulliEventProb p
        (fun Omega =>
          EventA Omega ∧ EventB Omega ∧ EventC Omega ∧ EventD Omega) ≥
      1 - (((cA + cB) + cC) + cD) * failureScale := by
  intro hp0 hp1 hA hB hC hD
  have hCD := inter2 p cC cD failureScale EventC EventD hp0 hp1 hC hD
  have hBCD := inter2 p cB (cC + cD) failureScale EventB
      (fun Ω => EventC Ω ∧ EventD Ω) hp0 hp1 hB hCD
  have hABCD := inter2 p cA (cB + (cC + cD)) failureScale EventA
      (fun Ω => EventB Ω ∧ EventC Ω ∧ EventD Ω) hp0 hp1 hA hBCD
  have hco : (cA + (cB + (cC + cD))) = (((cA + cB) + cC) + cD) := by ring
  rw [hco] at hABCD
  exact hABCD

-- Prove2me | solution 1 for NumberTheory.ExclusiveChannel.zeroAll_margin_ge_of_redundant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:44:27.98198+00:00
-- url     : https://prove2.me/submissions/7123bd0a-29d0-46d5-867f-01f1585ee62d

import Mathlib
import Definitions.Def_NumberTheory_ExclusiveChannelInterventions
open NumberTheory.ExclusiveChannel Finset in
theorem solution {k : ℕ} {b θ : ℝ} {g c : Fin k → ℝ} (hk : 0 < k)
    (hred : ∀ i, θ ≤ margin b g (zeroAt i c)) (hblock : ∑ i, g i * c i ≤ 0) :
    θ ≤ margin b g (zeroAll c) := by
  -- zeroing coordinate `i` removes exactly its contribution `g i * c i`
  have hz : ∀ i, margin b g (zeroAt i c) = b + (∑ j, g j * c j) - g i * c i := by
    intro i
    unfold margin zeroAt
    have e : ∀ j, g j * Function.update c i 0 j = g j * c j - (if j = i then g i * c i else 0) := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    simp only [e, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]
    ring
  have hall : margin b g (zeroAll c) = b := by
    unfold margin zeroAll
    simp
  rw [hall]
  -- average the `k` redundancy constraints
  have hsum : ∑ i : Fin k, θ ≤ ∑ i : Fin k, (b + (∑ j, g j * c j) - g i * c i) :=
    sum_le_sum (fun i _ => (hz i) ▸ hred i)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_sub_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

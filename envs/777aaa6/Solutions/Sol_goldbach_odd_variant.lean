-- Prove2me | solution 1 for goldbach_odd_variant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T08:22:07.88277+00:00
-- url     : https://prove2.me/submissions/716a8ec2-fcf4-4bc4-b8e6-20692593c8d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_strong_goldbach_conjecture

theorem solution :
    ∀ n : ℕ, 7 < n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  intro n hn hnot
  have hnotEven : ¬ Even n := by
    intro h
    rcases h with ⟨k, hk⟩
    apply hnot
    refine ⟨k, ?_⟩
    omega
  have hodd : Odd n := (Nat.not_even_iff_odd).mp hnotEven
  rcases hodd with ⟨k, hk⟩
  have hEvenSub : Even (n - 3) := by
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    strong_goldbach_conjecture (n - 3) (by omega) (by
      rcases hEvenSub with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      omega)
  refine ⟨p, q, 3, hp, hq, by norm_num, ?_⟩
  omega

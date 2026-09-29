-- Prove2me | solution 1 for kmer_repeat_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:39:52.853709+00:00
-- url     : https://prove2.me/submissions/5348b2c8-750f-4ec4-98a1-a2e2d9463141

import Mathlib
import Definitions.Def_Cryptography_RamseyTheory_KMerAvoidance
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    {n k : ℕ} (hn : Fintype.card α ^ k + k ≤ n) (s : Fin n → α) :
    ∃ i j : Fin (n - k + 1), i ≠ j ∧ kmer (by omega : k ≤ n) s i = kmer (by omega) s j := by
  -- more window positions than possible words: pigeonhole
  apply Fintype.exists_ne_map_eq_of_card_lt
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  omega

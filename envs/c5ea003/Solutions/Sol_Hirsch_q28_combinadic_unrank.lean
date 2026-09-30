-- Prove2me | solution 1 for Hirsch.q28_combinadic_unrank
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:32:52.98818+00:00
-- url     : https://prove2.me/submissions/e7feb826-5d66-4db6-b24a-35a3d638c5f6

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Classical Hirsch Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem unrankOk_true : unrankOk = true := rfl

lemma unrank_rank (s0 s1 s2 s3 s4 : ℕ)
    (h01 : s0 < s1) (h12 : s1 < s2) (h23 : s2 < s3) (h34 : s3 < s4) (h4 : s4 < 14) :
    unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4) := by
  have h := unrankOk_true
  simp [unrankOk, List.all_eq_true, List.mem_range] at h
  have hok := h s4 (by omega) s3 (by omega) s2 (by omega) s1 (by omega) s0 (by omega)
  simp at hok
  rcases hok with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4'⟩
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4')))

lemma combRank_lt (s0 s1 s2 s3 s4 : ℕ)
    (h01 : s0 < s1) (h12 : s1 < s2) (h23 : s2 < s3) (h34 : s3 < s4) (h4 : s4 < 14) :
    combRank s0 s1 s2 s3 s4 < 2002 := by
  have hs4 : s4 ≤ 13 := Nat.lt_succ_iff.mp h4
  have hs3 : s3 ≤ 12 := by omega
  have hs2 : s2 ≤ 11 := by omega
  have hs1 : s1 ≤ 10 := by omega
  have hs0 : s0 ≤ 9 := by omega
  have c5 : ch s4 5 ≤ 1287 := by
    revert s4 hs4 h4; intro s4 hs4 h4
    interval_cases s4 <;> simp [ch]
  have c4 : ch s3 4 ≤ 495 := by
    interval_cases s3 <;> simp [ch]
  have c3 : ch s2 3 ≤ 165 := by
    interval_cases s2 <;> simp [ch]
  have c2 : ch s1 2 ≤ 45 := by
    interval_cases s1 <;> simp [ch]
  have c1 : ch s0 1 ≤ 9 := by
    simp [ch]; omega
  simp [combRank]
  omega




theorem solution :
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) :=
  ⟨unrank_rank, combRank_lt⟩

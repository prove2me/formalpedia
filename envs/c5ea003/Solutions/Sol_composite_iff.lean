-- Prove2me | solution 1 for composite_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:41.718451+00:00
-- url     : https://prove2.me/submissions/8ab9e510-b33d-4e5f-93aa-d2912ddd5d8e

-- Sol generated from Algebra/Logic/ModelTheory.lean
import Mathlib

/-! # CatalogBuild.Logic.ModelTheory

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 10
-/












theorem solution(n : ℕ) (hn : 2 ≤ n) :
    ¬ Nat.Prime n ↔ ∃ d : ℕ, 2 ≤ d ∧ d < n ∧ d ∣ n := by
  constructor
  · intro h
    have hne : n ≠ 1 := by omega
    have hmf := Nat.minFac_prime hne
    have hmfd := Nat.minFac_dvd n
    refine ⟨n.minFac, ?_, ?_, hmfd⟩
    · exact hmf.two_le
    · by_contra hle
      push_neg at hle
      have : n.minFac = n := by
        apply le_antisymm (Nat.minFac_le (by omega)) hle
      exact h (this ▸ hmf)
  · rintro ⟨d, hd1, hd2, hd3⟩ hp
    have := hp.eq_one_or_self_of_dvd d hd3
    omega

-- Prove2me | solution 1 for Bridges.AlexanderTorus.divisors_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T14:42:09.384778+00:00
-- url     : https://prove2.me/submissions/8a13b30b-2808-4a43-bbf1-f3d827ec3b07

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_alexander_succ
import Theorems.Thm_Bridges_AlexanderTorus_odd_of_dvd_odd

open Bridges.AlexanderTorus Polynomial Finset

theorem solution {N : ℕ} (hpos : 0 < N) :
    (2 * N).divisors = N.divisors ∪ (N.divisors.image (fun d => 2 * d)) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hdvd, -⟩
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨e, rfl⟩ := he
      refine Or.inr ⟨e, ⟨?_, hpos.ne'⟩, by ring⟩
      have h : (2 : ℕ) * e ∣ 2 * N := by simpa [two_mul] using hdvd
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h
    · exact Or.inl ⟨Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 ho) hdvd,
        hpos.ne'⟩
  · rintro (⟨hdvd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
    · exact ⟨hdvd.mul_left 2, by positivity⟩
    · exact ⟨mul_dvd_mul_left 2 he, by positivity⟩

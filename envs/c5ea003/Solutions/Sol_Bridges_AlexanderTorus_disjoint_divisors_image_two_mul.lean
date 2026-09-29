-- Prove2me | solution 1 for Bridges.AlexanderTorus.disjoint_divisors_image_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T14:45:59.671443+00:00
-- url     : https://prove2.me/submissions/28e73bee-b6f3-4ce7-9eaf-9d6d83d611e8

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_alexander_succ
import Theorems.Thm_Bridges_AlexanderTorus_divisors_two_mul
import Theorems.Thm_Bridges_AlexanderTorus_odd_of_dvd_odd

open Bridges.AlexanderTorus Polynomial Finset

theorem solution {N : ℕ} (hN : Odd N) :
    Disjoint N.divisors (N.divisors.image (fun d => 2 * d)) := by
  rw [Finset.disjoint_right]
  rintro a ha ha'
  simp only [Finset.mem_image, Nat.mem_divisors] at ha ha'
  obtain ⟨e, -, rfl⟩ := ha
  obtain ⟨hdvd, -⟩ := ha'
  obtain ⟨k, hk⟩ := (dvd_mul_right 2 e).trans hdvd
  rw [Nat.odd_iff] at hN
  omega

/-! ## The cyclotomic factorization -/

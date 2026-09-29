-- Prove2me | solution 1 for TropicalDuality.ker_kme_eq_vanishing_support
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:05:37.905348+00:00
-- url     : https://prove2.me/submissions/22c25e39-fde7-4bc9-af87-f1caa7b364c8

import Mathlib
import Definitions.Def_Bridges_TropicalDuality

open TropicalDuality in
theorem solution {X : Type*} {S : Type*} [CommSemiring S] [Fintype X] [CommSemiring S]
    [SemilatticeSup S] [OrderBot S] [CommSemiring S] [DecidableEq X] [CommSemiring S]
    [Nontrivial S] [CommSemiring S] [DecidableEq X] [Nontrivial S] [Fintype X] [CommSemiring S]
    [SemilatticeSup S] [OrderBot S] [NoZeroDivisors S] (w : X → S)
    (hbot : (⊥ : S) = (0 : S)) :
    kmeKernel w = (vanishingIdeal (supportOfMeasure w) : Ideal (X → S)) := by
  ext f
  show kmeFromWeight w f = ⊥ ↔ ∀ x ∈ supportOfMeasure w, f x = 0
  unfold kmeFromWeight supportOfMeasure
  rw [Finset.sup_eq_bot_iff]
  simp only [Finset.mem_univ, true_implies, Set.mem_setOf_eq, hbot]
  constructor
  · intro h x hx
    exact (mul_eq_zero.1 (h x)).resolve_left hx
  · intro h x
    by_cases hx : w x = 0
    · rw [hx, zero_mul]
    · rw [h x hx, mul_zero]

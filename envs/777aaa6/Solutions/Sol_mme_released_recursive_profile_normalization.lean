-- Prove2me | solution 1 for mme_released_recursive_profile_normalization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:36:27.573143+00:00
-- url     : https://prove2.me/submissions/920cd6be-b625-49d8-b513-693803cd386a

import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
set_option maxRecDepth 3000

private theorem denominator_pos : (0 : ℝ) < D := by norm_num [D, MoreAsymmetryExactSeed.denominator]

attribute [local irreducible] regionCount regionWeight boundaryCount

theorem solution (t : SeedTerm) (i : Fin 3) (w : Word) :
    (parentCount t i w : ℝ) / (D : ℝ)^4 = parentProfile t i w := by
  unfold parentCount parentProfile
  split_ifs with h
  · simp only [Nat.cast_sum, Nat.cast_mul, regionProfile]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    ring
  · push_cast
    have hd := ne_of_gt denominator_pos
    field_simp

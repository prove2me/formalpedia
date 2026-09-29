-- Prove2me | solution 1 for mme_more_asymmetry_integer_regional_surplus_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:30:11.975909+00:00
-- url     : https://prove2.me/submissions/1983e664-454e-4998-b002-ea1f80f5dcfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_entropy_regional_surplus_certificate
import Theorems.Thm_mme_entropy_regional_recipe_compilation
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution :
    ∃ (N ell : ℕ) (P : Predicate N) (D : IntegerRecipe N ell P),
      1 ≤ D.a * D.b * D.c ∧
      ((D.inputs * 7 ^ N : ℕ) : ℝ) <
        (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by
  obtain ⟨N,ell,P,D,hpos,hsurplus⟩ := mme_more_asymmetry_entropy_regional_surplus_certificate
  obtain ⟨A,hAi,hAo,hAd⟩ := mme_entropy_regional_recipe_compilation D
  refine ⟨N,ell,P,A,?_,?_⟩
  · simpa only [IntegerRecipe.a,IntegerRecipe.b,IntegerRecipe.c,EntropyRecipe.a,EntropyRecipe.b,
      EntropyRecipe.c,hAd] using hpos
  · simpa only [hAi,hAo,IntegerRecipe.a,IntegerRecipe.b,IntegerRecipe.c,EntropyRecipe.a,EntropyRecipe.b,
      EntropyRecipe.c,hAd] using hsurplus

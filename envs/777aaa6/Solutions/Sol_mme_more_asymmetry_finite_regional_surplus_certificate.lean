-- Prove2me | solution 1 for mme_more_asymmetry_finite_regional_surplus_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:35:21.528673+00:00
-- url     : https://prove2.me/submissions/d387eb38-2ab7-4a86-a276-32276ecec66d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_integer_regional_surplus_certificate
import Theorems.Thm_mme_integer_regional_recipe_compilation

open MME MME.TensorObj MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution :
    ∃ (N ell : ℕ) (P : Predicate N) (D : RegionalPlan N ell P),
      1 ≤ D.a * D.b * D.c ∧
      ((D.inputs * 7 ^ N : ℕ) : ℝ) <
        (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by
  obtain ⟨N,ell,P,D,hpos,hsurplus⟩ := mme_more_asymmetry_integer_regional_surplus_certificate
  obtain ⟨A,hin,hout,hdim⟩ := mme_integer_regional_recipe_compilation D
  have ha : A.a = D.a := congrArg Prod.fst hdim
  have hb : A.b = D.b := congrArg (fun z ↦ z.2.1) hdim
  have hc : A.c = D.c := congrArg (fun z ↦ z.2.2) hdim
  exact ⟨N,ell,P,A,by simpa only [ha,hb,hc] using hpos,
    by simpa only [hin,hout,ha,hb,hc] using hsurplus⟩

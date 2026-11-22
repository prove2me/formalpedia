-- Prove2me | Theorems.Thm_mme_entropy_regional_smallN_no_surplus
-- name    : mme_entropy_regional_smallN_no_surplus
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-19T20:28:34.25374+00:00
-- url     : https://prove2.me/theorems/6a0b1ab6-28ef-4222-b224-3330a4fcee0a
-- title:
--   No surplus recipe at small N
-- statement:
--   Fix a level N <= 2 in the More Asymmetry regional setting. No finite entropy recipe D with one charged input satisfies the surplus inequality. In particular inputs(D) = 1 never yields inputs(D) * 7^N < outputs(D) * (a(D)b(D)c(D))^tau. Outputs are at most one by the small-N copy bound, dimensions multiply to at most 7^N by the boundary cap, and the remaining numerical check fails at each of N = 0, 1, 2. This delimits every surplus recipe to level at least three. Formalization Note Lean states the impossibility with explicit level and predicate binders over EntropyRecipe.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Small-N delimitation from the explicit copy and dimension bounds.

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_entropy_regional_smallN_no_surplus : forall (N ell : Nat) (P : MME.ProfiledCW.Predicate N) (D : EntropyRecipe N ell P), N <= 2 -> D.inputs = 1 -> ¬(((D.inputs * 7 ^ N : Nat) : Real) < (D.outputs : Real) * (((D.a * D.b * D.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) := by sorry

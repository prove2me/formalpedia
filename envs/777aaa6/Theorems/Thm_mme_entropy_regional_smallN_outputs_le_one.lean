-- Prove2me | Theorems.Thm_mme_entropy_regional_smallN_outputs_le_one
-- name    : mme_entropy_regional_smallN_outputs_le_one
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-19T10:24:00.144284+00:00
-- url     : https://prove2.me/theorems/223d86e2-8938-473a-af7b-1d7b96c707d0
-- title:
--   Small-N entropy recipes yield at most one output copy
-- statement:
--   Fix a level N <= 2 in the More Asymmetry regional setting. Every finite entropy recipe D at level N with one charged input type produces at most one output copy. In particular $$inputs(D)=1 \implies outputs(D) \le 1.$$ The descend case uses that every integer step at N <= 2 has zero entropy copies (at N=2 by the explicit rate-minus-losses estimate, at N=1 no step exists, at N=0 all counts vanish), so every descend level outputs zero; boundaries output one; partitions multiply. This delimits the search for surplus recipes to N >= 3. Formalization Note Lean states the bound with explicit level and predicate binders over EntropyRecipe.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Delimiting lemma proved from the explicit regional entropy copy bounds.

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_entropy_regional_smallN_outputs_le_one : forall (N ell : Nat) (P : MME.ProfiledCW.Predicate N) (D : EntropyRecipe N ell P), N <= 2 -> D.inputs = 1 -> D.outputs <= 1 := by sorry

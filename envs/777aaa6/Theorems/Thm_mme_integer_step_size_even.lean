-- Prove2me | Theorems.Thm_mme_integer_step_size_even
-- name    : mme_integer_step_size_even
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-19T12:41:42.56069+00:00
-- url     : https://prove2.me/theorems/a8605172-d09d-4a94-8293-39df0ce5967b
-- title:
--   Integer steps exist only at even sizes
-- statement:
--   In the More Asymmetry regional setting, every integer step lives at an even size M. In particular there is no integer step at any odd size, at any level, over any predicate. The length equation forces the number of physical positions to be even, and the size equals that count times a power of two. This rules out all odd-level descends with a positive number of types. Formalization Note Lean states evenness with explicit level, size and predicate binders over IntegerStep.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Parity obstruction from the length equation and the position census.

import Definitions.Def_mme_integer_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_integer_step_size_even : forall (lower M : Nat) (P : MME.ProfiledCW.Predicate M) (S : MME.RegionRealization.IntegerStep lower M P), Even M := by sorry

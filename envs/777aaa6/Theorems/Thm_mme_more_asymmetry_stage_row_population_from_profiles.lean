-- Prove2me | Theorems.Thm_mme_more_asymmetry_stage_row_population_from_profiles
-- name    : mme_more_asymmetry_stage_row_population_from_profiles
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T16:42:02.770647+00:00
-- url     : https://prove2.me/theorems/eeb9038d-2765-4ad7-98b1-4bcf86ec6f26
-- title:
--   Finite stage population from normalized profiles
-- statement:
--   Let $D=10^{12}$. Take 45 valid parent records with nonnegative integer weights whose total is $D$. At stage power $D^4$, a boundary parent contributes one block of size $D^3$ times its weight. A non-boundary parent is split across six inner regions; its combined row count is $D^2$ times its weight times the sum of its six region weights. The validity conditions make that region sum equal to $D$. The total population over all 45 parents is therefore exactly $D^4$. This identity supplies the finite position count used when forming the six recursive stages; it does not assert a hash, a matrix restriction, or the stage budget bounds.
-- source:
--   Exact integerization of MME.MoreAsymmetryExactSeed.Term.Valid from More Asymmetry, arXiv:2404.16349v2, Sections 5.1 and 6.1, using the pinned W1.00_2.371339.mat table (SHA-256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3). The normalized profile validity theorem is mme_more_asymmetry_released_exact_profile_seed_valid (87a4b7d4-04ba-4e88-835b-c15dca0975c0).

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

open BigOperators MME.MoreAsymmetryExactSeed
set_option autoImplicit false

theorem mme_more_asymmetry_stage_row_population_from_profiles (t : Fin 45 → Term) (w : Fin 45 → ℕ) (ht : ∀ i, (t i).Valid) (hw : ∑ i : Fin 45, w i = denominator) : (∑ i : Fin 45, if (t i).boundary = [] then denominator ^ 2 * w i * (t i).region.sum else denominator ^ 3 * w i) = denominator ^ 4 := by sorry

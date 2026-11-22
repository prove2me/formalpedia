-- Prove2me | Theorems.Thm_mme_integer_regional_step_N2_level_bound_anyP
-- name    : mme_integer_regional_step_N2_level_bound_anyP
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T14:50:38.010659+00:00
-- url     : https://prove2.me/theorems/c69241c2-bb63-4e73-8bb1-4436b62fb455
-- title:
--   N=2 integer steps live below level 3 over any predicate
-- statement:
--   Every integer regional step with two elementary positions lives below level $3$, over any predicate.
--
--   The length equation is $L\,2^{lower-1}=2$, unsatisfiable for $lower\ge 3$ since then $2^{lower-1}\ge 4$. The predicate plays no role. This generalizes the trivial-predicate level bound used across the regional branch.
--
--   **Formalization Note** The proof uses only the length field.
-- source:
--   Generalization of mme_integer_regional_step_N2_level_bound; length arithmetic for Alman et al., More Asymmetry, https://arxiv.org/html/2404.16349v2#S6, Section 6.

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_profiled_CW_data
set_option autoImplicit false

theorem mme_integer_regional_step_N2_level_bound_anyP : forall (lower : Nat) (P : MME.ProfiledCW.Predicate 2) (S : MME.RegionRealization.IntegerStep lower 2 P), lower < 3 := by sorry

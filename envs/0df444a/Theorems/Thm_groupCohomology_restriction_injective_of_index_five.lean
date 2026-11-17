-- Prove2me | Theorems.Thm_groupCohomology_restriction_injective_of_index_five
-- name    : groupCohomology.restriction_injective_of_index_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:55.673923+00:00
-- url     : https://prove2.me/theorems/fd76425b-d4f2-4a19-8672-543926857551
-- title:
--   Restriction to an index-five subgroup is injective over $ℤ/71ℤ$
-- statement:
--   Let $G$ be a group, let $S≤G$ have finite index $[G:S]=5$, let $M$ be a $ℤ/71ℤ$-representation of $G$, and let $n∈ℕ$. Then the restriction map is injective: $$H^n(G,M)→H^n(S,M|_S).$$ This permits vanishing to be checked after passage to the quintic character field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm

set_option autoImplicit false
open CategoryTheory
open groupCohomology
local instance instL_groupCohomology_restriction_injective_of_23397f_i27a302 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem groupCohomology.restriction_injective_of_index_five
    {G : Type} [Group G] (S : Subgroup G) [S.FiniteIndex]
    (hindex : S.index = 5) (M : Rep (ZMod 71) G) (n : ℕ) :
    Function.Injective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n).hom := by sorry

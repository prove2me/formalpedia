-- Prove2me | Theorems.Thm_mme_recursive_regional_CW_plan_sound
-- name    : mme_recursive_regional_CW_plan_sound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T15:17:39.442296+00:00
-- url     : https://prove2.me/theorems/bdae200c-4119-46fa-8257-4e8cbf89f036
-- title:
--   Full regional CW recursion yields its exactly counted matrix copies
-- statement:
--   Let $D$ be a finite recursive recipe on an actual projected power $\operatorname{CW}_5^N[P]$. Its steps may extract and cover exact profile types, recurse jointly to lower levels, partition positions into independently processed regions, and change any of the six mode roles. Write $I(D),O(D)$ for its computed input and output counts and $a(D),b(D),c(D)$ for its terminal matrix dimensions. Then, over every field,
--
--   $$\bigoplus_{O(D)}\langle a(D),b(D),c(D)\rangle\ \le\ \bigoplus_{I(D)}\operatorname{CW}_5^N[P].$$
--
--   Every copy cost and output multiplicity is retained. The recipe stores only finite combinatorial data and profile predicates, not assumed tensor maps. This soundness theorem does not assert existence of a recipe meeting a particular numerical bound.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3, Theorem 6.4, and Section 7. Finite constructive soundness with explicit profile, hole, coverage and source-copy hypotheses; numerical witness not supplied.

import Definitions.Def_mme_recursive_regional_CW_data
open MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_recursive_regional_CW_plan_sound {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : RegionalPlan N ell P) :
    Restrict (bigAdd (fun _ : Fin D.outputs ↦ MMObj K D.a D.b D.c))
      (bigAdd (fun _ : Fin D.inputs ↦ tensor K P)) := by sorry

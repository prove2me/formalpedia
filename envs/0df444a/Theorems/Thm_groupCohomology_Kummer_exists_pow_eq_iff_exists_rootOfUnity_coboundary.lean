-- Prove2me | Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary
-- name    : groupCohomology.Kummer.exists_pow_eq_iff_exists_rootOfUnity_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/7dd90891-4cd1-5a2f-a4fd-7dd452064c27
-- title:
--   Kummer cocycle is a coboundary of a root of unity
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra which is Galois over $K$ (in the sense of Mathlib's `IsGalois`, so possibly of infinite degree), let $p$ be a natural number, and let $a \in K^\times$ and $\alpha \in L^\times$ be units satisfying $\operatorname{algebraMap}_{K\to L}(a) = \alpha^p$ in $L$. The assertion is the equivalence of the following two statements: (i) there is a unit $b \in K^\times$ with $b^p = a$; (ii) there is a unit $\zeta \in L^\times$ with $\zeta^p = 1$ such that for every $K$-algebra automorphism $\sigma$ of $L$ one has $(\sigma \cdot \zeta)/\zeta = \mathtt{kummerCocycle}\,\alpha\,\sigma$, where the latter is by definition $(\sigma \cdot \alpha)/\alpha$, the action being the natural action of $L \simeq_{\text{alg}[K]} L$ on $L^\times$. Thus $a$ is a $p$-th power in $K^\times$ exactly when the map $\sigma \mapsto \sigma(\alpha)/\alpha$ is the coboundary of an element of $L^\times$ whose $p$-th power is $1$. No primality or positivity assumption is imposed on $p$, and no finiteness assumption on $L/K$.
--
--   This is the element-wise description of the kernel of the Kummer map, the constraint $\zeta^p = 1$ being the whole content, since a coboundary witness in $L^\times$ exists unconditionally by construction of the cocycle. It is used in the project's Kummer-theory layer, in particular for the criterion [`groupCohomology.Kummer.exists_pow_eq_iff_of_fixingSubgroup`](thm.html#groupCohomology.Kummer.exists_pow_eq_iff_of_fixingSubgroup), for the vanishing criterion [`groupCohomology.Kummer.kummerClass_eq_zero_iff`](thm.html#groupCohomology.Kummer.kummerClass_eq_zero_iff) for the Kummer class, and in the bound [`groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two`](thm.html#groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.exists_pow_eq_iff_exists_rootOfUnity_coboundary
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔
      ∃ ζ : Lˣ, ζ ^ p = 1 ∧ ∀ σ : L ≃ₐ[K] L, σ • ζ / ζ = kummerCocycle α σ := by sorry

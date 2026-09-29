-- Prove2me | Theorems.Thm_exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add
-- name    : exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/617a68b5-b789-51c8-830a-e9291da7547d
-- title:
--   Globalising a homomorphism defined on a ball
-- statement:
--   Let $V$ be a real normed vector space (a normed additive commutative group with a compatible $\mathbb{R}$-module structure), let $A$ be a group, let $r$ be a real number with $0 < r$, and let $e_0 : V \to A$ be an arbitrary function, subject to the single hypothesis that $e_0$ is additive-to-multiplicative wherever all three arguments lie in the open ball of radius $r$: for all $v, w \in V$ with $\lVert v\rVert < r$, $\lVert w\rVert < r$ and $\lVert v + w\rVert < r$ one has $e_0(v + w) = e_0(v)\,e_0(w)$. The conclusion asserts that there exists a unique monoid homomorphism $e : \mathrm{Multiplicative}\,V \to A$ — that is, a homomorphism from the additive group of $V$ written multiplicatively, into $A$ — such that $e(\mathrm{ofAdd}\,v) = e_0(v)$ for every $v \in V$ with $\lVert v\rVert < r$. Uniqueness is uniqueness in the sense of `ExistsUnique`: any monoid homomorphism agreeing with $e_0$ on the ball of radius $r$ equals $e$. No topology or continuity is imposed on $A$, and no continuity of $e_0$ is assumed.
--
--   This is the standard globalisation of a local homomorphism defined on a ball of a real normed space: since the ball generates the additive group and the space is divisible, a partial homomorphism extends uniquely to the whole group. It is used in the construction of the complex uniformisation of abelian varieties, where the global exponential map is obtained from a locally defined one; it is cited by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology

theorem exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Type*} [Group A]
    {r : ℝ} (hr : 0 < r) (e₀ : V → A)
    (h : ∀ v w : V, ‖v‖ < r → ‖w‖ < r → ‖v + w‖ < r → e₀ (v + w) = e₀ v * e₀ w) :
    ∃! e : Multiplicative V →* A, ∀ v : V, ‖v‖ < r → e (Multiplicative.ofAdd v) = e₀ v := by sorry

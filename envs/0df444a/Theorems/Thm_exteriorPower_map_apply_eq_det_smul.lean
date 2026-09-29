-- Prove2me | Theorems.Thm_exteriorPower_map_apply_eq_det_smul
-- name    : exteriorPower.map_apply_eq_det_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/e0228578-2f0b-590c-947b-a23f7dab48a9
-- title:
--   Top exterior power of an endomorphism is multiplication by det
-- statement:
--   Let $A$ be a commutative ring and $M$ an $A$-module (an additive commutative group with an $A$-module structure), let $\iota$ be a finite type and $b$ a basis of $M$ indexed by $\iota$, let $n$ be a natural number with $\operatorname{card}(\iota) = n$, and let $f : M \to M$ be an $A$-linear endomorphism. Then for every element $x$ of the $n$-th exterior power $\bigwedge[A]^n M$, the induced map `exteriorPower.map n f` on the $n$-th exterior power sends $x$ to $\det(f) \cdot x$, where $\det(f)$ is the determinant of $f$ as a linear map (Mathlib's `LinearMap.det`) and the product is the $A$-scalar action on $\bigwedge[A]^n M$. Thus under the hypothesis that $M$ is free of rank $n$ with basis indexed by an arbitrary finite type of cardinality $n$, the endomorphism $\bigwedge^n f$ of the top exterior power is scalar multiplication by $\det f$; no freeness or rank-one statement about $\bigwedge[A]^n M$ itself is asserted, and the equality is stated pointwise in $x$ rather than as an equality of linear maps.
--
--   This is the standard identity $\bigwedge^{\mathrm{top}} f = \det f$ for an endomorphism of a free module of finite rank $n$. It is used in the project by [`exteriorPower.map_mulLeft_apply_eq_norm_smul`](thm.html#exteriorPower.map_mulLeft_apply_eq_norm_smul), where the determinant of the multiplication-by-an-element endomorphism is identified with a norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exteriorPower_map_apply_eq_det_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exteriorPower.map_apply_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) {n : ℕ} (hn : Fintype.card ι = n)
    (f : M →ₗ[A] M) (x : ⋀[A]^n M) :
    exteriorPower.map n f x = LinearMap.det f • x := by sorry

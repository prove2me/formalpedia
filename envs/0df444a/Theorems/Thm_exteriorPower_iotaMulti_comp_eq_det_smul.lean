-- Prove2me | Theorems.Thm_exteriorPower_iotaMulti_comp_eq_det_smul
-- name    : exteriorPower.iotaMulti_comp_eq_det_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/171a3c7f-716a-50ce-b1cd-5a8149867f40
-- title:
--   Top wedge of images under an endomorphism is det f times the wedge
-- statement:
--   Let $A$ be a commutative ring and $M$ an $A$-module (given as an additive commutative group with an $A$-module structure), let $n$ be a natural number, and suppose $b$ is an $A$-basis of $M$ indexed by `Fin n`, so that $M$ is free of rank $n$. Let $f \colon M \to M$ be an $A$-linear endomorphism and let $m \colon \mathrm{Fin}\,n \to M$ be an arbitrary family of $n$ elements of $M$, subject to no further condition. The assertion is an identity in the $n$-th exterior power $\bigwedge^n_A M$: the value of the canonical alternating map `exteriorPower.ιMulti A n` on the composed family $f \circ m$, that is $f(m_0) \wedge \cdots \wedge f(m_{n-1})$, equals the scalar $\mathrm{LinearMap.det}\,f$ acting by scalar multiplication on the value of the same map on $m$, that is $\det(f) \cdot (m_0 \wedge \cdots \wedge m_{n-1})$. The basis $b$ enters only as a hypothesis guaranteeing freeness of rank $n$; the determinant is the Mathlib determinant of a linear endomorphism.
--
--   This is the module-level form of the classical statement that the $n$-th exterior power of an endomorphism of a free module of rank $n$ is multiplication by its determinant. It is used to derive [`exteriorPower.map_apply_eq_det_smul`](thm.html#exteriorPower.map_apply_eq_det_smul), and in that form underlies the identification of top exterior powers with determinant, respectively norm, twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exteriorPower_iotaMulti_comp_eq_det_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exteriorPower.iotaMulti_comp_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) (f : M →ₗ[A] M) (m : Fin n → M) :
    exteriorPower.ιMulti A n (f ∘ m) = LinearMap.det f • exteriorPower.ιMulti A n m := by sorry

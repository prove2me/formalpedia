-- Prove2me | Theorems.Thm_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range
-- name    : finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/388c743c-dfe2-54a1-87b6-6f5a2d18b4c1
-- title:
--   ℚ⊗ O is a quaternion division algebra with centre ℚ
-- statement:
--   Let $O$ be a ring which is a domain (no zero divisors, and nontrivial), free and finite as a $\mathbb{Z}$-module, with $\operatorname{finrank}_{\mathbb{Z}} O = 4$, and let $\ell$ be a prime such that there exists an isomorphism of $\mathbb{Z}_{\ell}$-algebras $\mathbb{Z}_{\ell}\otimes_{\mathbb{Z}} O \cong M_2(\mathbb{Z}_{\ell})$ (the hypothesis is the nonemptiness of the type of such `AlgEquiv`s, so no particular isomorphism is named). Then the $\mathbb{Q}$-algebra $D := \mathbb{Q}\otimes_{\mathbb{Z}} O$ satisfies three assertions simultaneously: first, $\operatorname{finrank}_{\mathbb{Q}} D = 4$; second, every nonzero $x \in D$ is a unit of $D$, i.e. $D$ is a division ring; and third, every $z \in D$ commuting with all $x \in D$ (that is, $z x = x z$ for all $x$) lies in the range of the structure map $\mathbb{Q} \to D$, so the centre of $D$ is no larger than the image of $\mathbb{Q}$. Non-commutativity of $D$ is not part of the conclusion; the third clause is the one-sided inclusion $Z(D) \subseteq \mathbb{Q}\cdot 1$.
--
--   This is the recognition step saying that a rank-four $\mathbb{Z}$-order without zero divisors having one matrix completion rationalises to a quaternion algebra over $\mathbb{Q}$: a four-dimensional central division algebra over $\mathbb{Q}$. It feeds the construction of definite quaternion algebras ramified exactly at a prescribed set of places together with a maximal order, used further on in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range
    (O : Type*) [Ring O] [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hrank : Module.finrank ℤ O = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ])) :
    Module.finrank ℚ (ℚ ⊗[ℤ] O) = 4 ∧
      (∀ x : ℚ ⊗[ℤ] O, x ≠ 0 → IsUnit x) ∧
      (∀ z : ℚ ⊗[ℤ] O, (∀ x : ℚ ⊗[ℤ] O, z * x = x * z) →
        z ∈ Set.range (algebraMap ℚ (ℚ ⊗[ℤ] O))) := by sorry

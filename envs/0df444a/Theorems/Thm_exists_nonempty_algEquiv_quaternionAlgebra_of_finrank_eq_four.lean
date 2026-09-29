-- Prove2me | Theorems.Thm_exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four
-- name    : exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c3f54e8b-8b05-58a7-8aab-eed6c2edc1a9
-- title:
--   Four-dimensional central division ℚ-algebras are quaternion algebras
-- statement:
--   Let $D$ be a ring equipped with a $\mathbb{Q}$-algebra structure, subject to three hypotheses: $D$ has dimension $4$ as a $\mathbb{Q}$-vector space; every nonzero element of $D$ is a unit; and every element $z$ of $D$ that commutes with all elements of $D$ lies in the image of the structure map $\mathbb{Q} \to D$, i.e. the centre of $D$ is no larger than $\mathbb{Q}$. The conclusion is that there exist rational numbers $a$ and $b$, both nonzero, together with an isomorphism of $\mathbb{Q}$-algebras between $D$ and the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$, that is, the $\mathbb{Q}$-algebra with basis $1, i, j, ij$ and relations $i^2 = a$, $j^2 = b$, $ji = -ij$. The existence of the isomorphism is recorded as the nonemptiness of the type of $\mathbb{Q}$-algebra equivalences $D \simeq_{\mathbb{Q}} \mathbb{H}[\mathbb{Q}, a, b]$, so the statement asserts that some such pair $(a,b)$ of nonzero rationals and some isomorphism exist, without producing them as data.
--
--   This is the standard recognition theorem for quaternion algebras: a central division algebra of degree $4$ over a field of characteristic zero is of the form $(a,b)$. It is used in the construction of definite quaternion algebras over $\mathbb{Q}$ ramified exactly at a prescribed set of places, via [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four
    (D : Type*) [Ring D] [Algebra ℚ D] (hdim : Module.finrank ℚ D = 4)
    (hdiv : ∀ x : D, x ≠ 0 → IsUnit x)
    (hcen : ∀ z : D, (∀ x : D, z * x = x * z) → z ∈ Set.range (algebraMap ℚ D)) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (D ≃ₐ[ℚ] ℍ[ℚ, a, b]) := by sorry

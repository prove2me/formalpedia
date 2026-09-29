-- Prove2me | Theorems.Thm_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
-- name    : exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/6d705cf4-6c42-57c5-afe2-fdf859fc177c
-- title:
--   Orthogonal idempotents from a prime-order endomorphism
-- statement:
--   Let $F$ be a field and $A$ a commutative ring which is an $F$-algebra, finite as an $F$-module and reduced (its nilradical is zero). Let $s \colon A \to A$ be a ring homomorphism, and let $n$ be a prime number such that the $n$-fold iterate of the underlying map of $s$ is the identity on $A$. Assume that every element fixed by $s$, that is every $a \in A$ with $s(a) = a$, lies in the image of the structure map $F \to A$. Assume finally that $A$ is not a field. Then there exists $e \in A$ with $e^2 = e$ such that $e \cdot s^i(e) = 0$ for every index $i$ with $0 < i < n$, and such that $\sum_{i=0}^{n-1} s^i(e) = 1$, the iterates being those of the underlying function of $s$. Thus $e, s(e), \dots, s^{n-1}(e)$ form a complete family of pairwise orthogonal (by the stated relations together with the action of the iterates of $s$) idempotents summing to $1$, so that $A$ decomposes as a product of $n$ copies of $eA$ permuted cyclically by $s$.
--
--   This is the structural input for a descent argument concerning a finite reduced algebra over a field carrying an endomorphism of prime order whose fixed ring is as small as possible: either the algebra is a field, or it splits into $n$ factors cyclically permuted by the endomorphism. It is cited by [`IsDedekindDomain.HeightOneSpectrum.exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm`](thm.html#IsDedekindDomain.HeightOneSpectrum.exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
    (F A : Type) [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A]
    (s : A →+* A) (n : ℕ) (hn : n.Prime) (hsn : (⇑s)^[n] = id)
    (hfix : ∀ a : A, s a = a → a ∈ Set.range (algebraMap F A))
    (hA : ¬ IsField A) :
    ∃ e : A, IsIdempotentElem e ∧ (∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) ∧
      (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1 := by sorry

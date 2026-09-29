-- Prove2me | Theorems.Thm_HefferonLinAlg_change_of_basis_gives_similar_matrices
-- name    : HefferonLinAlg.change_of_basis_gives_similar_matrices
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:34:04.093834+00:00
-- url     : https://prove2.me/theorems/b8d8f63b-1a07-44fb-a107-872900660bcf
-- title:
--   Change of basis is similarity
-- statement:
--   Let $t : V \to V$ be a linear transformation of an $n$-dimensional vector space over a field $K$, and let $B$ and $C$ be bases of $V$. Then there is an invertible matrix $P$ with $\mathrm{Rep}_{C,C}(t) = P^{-1}\,\mathrm{Rep}_{B,B}(t)\,P$: the two matrices representing the same transformation with respect to different bases are similar. This is the hinge of the book — it turns the search for a canonical form for similarity into the search for the basis in which a map looks simplest, which is the whole programme of Chapter Five.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Three, Section V.2, Corollary 2.5, p. 280

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem change_of_basis_gives_similar_matrices
    {K : Type*} [Field K] {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (B C : Module.Basis (Fin n) K V) (t : V →ₗ[K] V) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P.det ∧
      LinearMap.toMatrix C C t = P⁻¹ * LinearMap.toMatrix B B t * P := by
  sorry

end HefferonLinAlg

-- Prove2me | Theorems.Thm_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
-- name    : exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/03549279-f8ef-5597-9d3e-a36e6a81b665
-- title:
--   Lagrange idempotents for a root of unity over a commutative ring
-- statement:
--   Let $R$ be a commutative ring and $N$ a natural number, and write $m = N+1$. Assume the image of $m$ in $R$ is a unit; let $\zeta \in R$ satisfy $\zeta^{m} = 1$ together with the strong primitivity condition that $1 - \zeta^{j}$ is a unit of $R$ for every $j$ with $0 < j < m$; and let $\omega \in R$ satisfy $\omega^{m} = 1$. The conclusion is that there exists a family $e : \mathrm{Fin}(m) \to R$ which is a complete family of orthogonal idempotents in the sense of Mathlib's `CompleteOrthogonalIdempotents`, i.e. each $e_k$ is idempotent, $e_k e_l = 0$ for $k \ne l$, and $\sum_{k} e_k = 1$, and which diagonalises $\omega$ in the sense that $\omega \, e_k = \zeta^{k} e_k$ for every $k \in \mathrm{Fin}(m)$, where $k$ is read as a natural number in the exponent. No connectedness or local hypothesis on $R$ is imposed, and no uniqueness is asserted.
--
--   This is the Lagrange-resolvent decomposition: over a ring in which $N+1$ is invertible and $\zeta$ is a strong primitive $(N+1)$-st root of unity, $\operatorname{Spec} R$ splits into $N+1$ complementary open pieces on the $k$-th of which a given $(N+1)$-st root of unity $\omega$ equals $\zeta^{k}$. It is used in the theta-structure material, for instance to decompose a ring according to the values of an additive character and to diagonalise Schrödinger-type matrices, and is the base case of the corresponding statement for families of commuting roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
    (R : Type u) [CommRing R] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : R))
    (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : R) (hω : ω ^ (N + 1) = 1) :
    ∃ e : Fin (N + 1) → R, CompleteOrthogonalIdempotents e ∧ ∀ k : Fin (N + 1), ω * e k = ζ ^ (k : ℕ) * e k := by sorry

-- Prove2me | Theorems.Thm_WittVector_isWeightedHomogeneous_wittStructureInt
-- name    : WittVector.isWeightedHomogeneous_wittStructureInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a7bcdaaf-c05a-5685-b5cd-b74a77b8c42c
-- title:
--   Witt structure polynomials are weighted homogeneous
-- statement:
--   Let $p$ be a prime, let $idx$ be a type, let $\Phi \in \mathbb{Z}[(X_b)_{b \in idx}]$ be a multivariate polynomial over $\mathbb{Z}$, let $k$ be a natural number, and assume $\Phi$ is homogeneous of degree $k$, i.e. every monomial in the support of $\Phi$ has total degree $k$. Let $n$ be a natural number. Then the $n$-th integral Witt structure polynomial $\mathrm{wittStructureInt}\,p\,\Phi\,n \in \mathbb{Z}[(X_{b,i})_{(b,i) \in idx \times \mathbb{N}}]$ is weighted homogeneous of weighted degree $k \cdot p^n$ for the weight function assigning to the variable indexed by $(b,i)$ the weight $p^i$: that is, for every monomial $d \colon idx \times \mathbb{N} \to \mathbb{N}$ (of finite support) whose coefficient in $\mathrm{wittStructureInt}\,p\,\Phi\,n$ is non-zero, one has $\sum_{(b,i)} d(b,i)\, p^i = k \cdot p^n$. As is usual for this predicate, the condition is vacuous on monomials not occurring, so the zero polynomial satisfies it for any degree.
--
--   This is the classical statement that the Witt structure (universal) polynomials attached to a homogeneous $\Phi$ of degree $k$ are isobaric of weight $k p^n$ when the variable $X_{b,i}$ is given weight $p^i$; for $\Phi = X_0 + X_1$ it says that the Witt addition polynomials have weight $p^n$. It is used in the project to control the carries in Witt-vector addition, namely by [`WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow`](thm.html#WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_isWeightedHomogeneous_wittStructureInt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v

theorem WittVector.isWeightedHomogeneous_wittStructureInt
    (p : ℕ) [Fact p.Prime] {idx : Type v} (Φ : MvPolynomial idx ℤ) (k : ℕ) (hΦ : Φ.IsHomogeneous k)
    (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2) (wittStructureInt p Φ n)
      (k * p ^ n) := by sorry

-- Prove2me | Theorems.Thm_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
-- name    : fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a6db2767-3588-53a4-9708-edec901a5683
-- title:
--   Vanishing (d+1)-st forward difference characterises numerical polynomials
-- statement:
--   Let $R$ be a field of characteristic zero, let $f \colon \mathbb{Z} \to R$ be an arbitrary function and let $d$ be a natural number. Here `fwdDiff (1 : ℤ)` is the forward difference operator with step $1$ on functions $\mathbb{Z} \to R$, sending $f$ to $n \mapsto f(n+1) - f(n)$, and `(fwdDiff (1 : ℤ))^[d + 1]` is its $(d+1)$-fold iterate. The theorem asserts the equivalence of two statements: first, that the iterated difference $\Delta^{d+1} f$ vanishes at every integer $n$; and second, that there exists a polynomial $p \in R[X]$ whose `natDegree` is at most $d$ and which satisfies $f(n) = p(n)$, the evaluation being at the image of $n$ under the canonical map $\mathbb{Z} \to R$, for every integer $n$. Note that the degree bound is stated for `natDegree`, so for $d = 0$ it allows exactly the constant functions; no regularity or growth hypothesis on $f$ is imposed, and agreement of $f$ with $p$ is required on all of $\mathbb{Z}$, not merely on the non-negative integers.
--
--   This is the basic algebraic lemma of the theory of numerical polynomials: a function on $\mathbb{Z}$ is polynomial of degree at most $d$ exactly when its $(d+1)$-st finite difference vanishes identically. It is used in the project to show that the Euler characteristics $n \mapsto \chi(\mathcal{F} \otimes \mathcal{L}^{\otimes n})$ of twists of a module presheaf are given by a polynomial in $n$, with control on its degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
    {R : Type*} [Field R] [CharZero R] (f : ℤ → R) (d : ℕ) :
    (∀ n : ℤ, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) ↔
      ∃ p : Polynomial R, p.natDegree ≤ d ∧ ∀ n : ℤ, f n = p.eval (n : R) := by sorry

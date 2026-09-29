-- Prove2me | Theorems.Thm_Zeta23_MV_eigen_identityPrime
-- name    : Zeta23.MV.eigen_identityPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:52:10.031589+00:00
-- url     : https://prove2.me/theorems/32ec0da9-b9af-40b5-a23f-66e884bd5f50
-- title:
--   Preissmann–Lévêque eigen-identity for the skew kernel $c_m c_n/(\lambda_m - \lambda_n)$
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq} \colon \iota \to \mathbb{R}$ injective, and $c \colon \iota \to \mathbb{R}$ with $c_r > 0$ for all $r$. Let $u \colon \iota \to \mathbb{C}$ and $\mu \in \mathbb{R}$ satisfy the eigen-relation for the skew-Hermitian kernel $H_{mn} = c_m c_n/(\mathrm{freq}_m - \mathrm{freq}_n)$ ($m \ne n$):
--
--   $$\sum_{n \ne m} \frac{c_m c_n}{\mathrm{freq}_m - \mathrm{freq}_n}\, u_n \;=\; \mu\, i\, u_m \qquad \text{for every } m.$$
--
--   Then for every index $m$,
--
--   $$\mu^2\, \|u_m\|^2 \;=\; \sum_{n \ne m} \frac{(c_m c_n)^2\, \|u_n\|^2}{(\mathrm{freq}_m - \mathrm{freq}_n)^2} \;+\; 2 \sum_{n \ne m} \frac{c_m^3\, c_n\, \operatorname{Re}\bigl(u_m\, \overline{u_n}\bigr)}{(\mathrm{freq}_m - \mathrm{freq}_n)^2}.$$
--
--   This is Lemma 2.1 of Preissmann–Lévêque (arXiv:2203.14950), proved by pure finite algebra: expand $|\mu u_m|^2$ as a double sum, apply the partial-fraction identity $\frac{1}{(\lambda_m-\lambda_n)(\lambda_m-\lambda_p)} = \frac{1}{(\lambda_m-\lambda_n)(\lambda_n-\lambda_p)} - \frac{1}{(\lambda_m-\lambda_p)(\lambda_n-\lambda_p)}$ off the diagonal, and use the conjugate eigen-relation; the purely imaginary $-i\mu\|u_n\|^2/c_n$ piece dies under the real part — the cancellation at the heart of Montgomery–Vaughan.
--
--   **Role.** Step 2 of the Montgomery–Vaughan chain: it is consumed by `Zeta23.MV.eigen_bound`, which specializes $c = \sqrt{\delta}$, sums over $m$, and inserts the spacing bounds to conclude $|\mu| \le 13$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/EigenIdentity.lean#L46-L190, docstring reference arXiv:2203.14950 Lemma 2.1

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic

open Finset Complex
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}

theorem Zeta23.MV.eigen_identityPrime (hinj : Function.Injective freq) (c : ι → ℝ) (hc : ∀ r, 0 < c r)
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((c m * c n / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m)
    (m : ι) :
    μ ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
      + 2 * ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2 := by sorry

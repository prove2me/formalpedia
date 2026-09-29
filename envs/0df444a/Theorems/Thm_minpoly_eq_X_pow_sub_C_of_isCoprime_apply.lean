-- Prove2me | Theorems.Thm_minpoly_eq_X_pow_sub_C_of_isCoprime_apply
-- name    : minpoly.eq_X_pow_sub_C_of_isCoprime_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/a77e948e-c3b0-53e9-911c-df631b81ff7d
-- title:
--   Minimal polynomial of an n-th root Xⁿ - C u
-- statement:
--   Let $F$ be a field and $L$ a nontrivial ring carrying an $F$-algebra structure. Let $v \colon F \to \mathbb{Z}$ be any function which is additive on products of nonzero elements, i.e. $v(xy) = v(x) + v(y)$ for all $x, y \in F$ with $x \neq 0$ and $y \neq 0$; no further structure on $v$ is assumed (in particular it need not be a valuation). Let $n$ be a natural number with $0 < n$, and let $u \in F$ be nonzero with $v(u)$ and $n$ coprime as integers, in the Bézout sense of `IsCoprime` (there exist integers $a, b$ with $a\,v(u) + b\,n = 1$; for integers this is equivalent to $\gcd(v(u), n) = 1$). Let $\theta \in L$ satisfy $\theta^n = u$, more precisely $\theta^n$ equals the image of $u$ under the structure map $F \to L$. Then the minimal polynomial of $\theta$ over $F$ is exactly $X^n - C u$. In particular $\theta$ is algebraic over $F$ and, $X^n - C u$ being monic of degree $n$, the degree of $\theta$ over $F$ is $n$.
--
--   This is the standard statement that a radical (Kummer) extension $F(\sqrt[n]{u})$ has degree exactly $n$ as soon as some additive-on-products integer-valued invariant of $u$ is prime to $n$, the usual criterion for total ramification in the function-field setting; no hypotheses on roots of unity, on the characteristic, or on $n$ beyond positivity are needed, and $L$ is only required to be a nontrivial $F$-algebra. It is used in the analysis of the Drinfeld curve, for instance in [`DrinfeldCurve.affinePlaces_census`](thm.html#DrinfeldCurve.affinePlaces_census) and [`DrinfeldCurve.genusFF_drinfeldFunctionField`](thm.html#DrinfeldCurve.genusFF_drinfeldFunctionField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_minpoly_eq_X_pow_sub_C_of_isCoprime_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem minpoly.eq_X_pow_sub_C_of_isCoprime_apply
    {F L : Type*} [Field F] [Ring L] [Nontrivial L] [Algebra F L]
    (v : F → ℤ) (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {u : F} (hu : u ≠ 0) (hcop : IsCoprime (v u) n)
    (θ : L) (hθ : θ ^ n = algebraMap F L u) :
    minpoly F θ = X ^ n - C u := by sorry

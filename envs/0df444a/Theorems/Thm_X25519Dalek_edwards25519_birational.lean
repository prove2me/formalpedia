-- Prove2me | Theorems.Thm_X25519Dalek_edwards25519_birational
-- name    : X25519Dalek.edwards25519_birational
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T22:37:14.8368+00:00
-- url     : https://prove2.me/theorems/bed94bfc-5145-429b-b44a-3637dd38bb35
-- title:
--   RFC 7748 §4.1 — curve25519 and edwards25519 are birationally equivalent by the stated maps
-- statement:
--   Three statements over $\mathbb{F}_p$, $p = 2^{255} - 19$, with all arithmetic mod $p$ and division taken as multiplication by the power $p - 2$ (bundle `X25519Dalek_Rfc7748`).
--   - **A square root of $-486664$ exists:** some $s < p$ has $s^2 \equiv -486664$.
--   - **For every such $s$, the maps are mutually inverse between the two curves.** For every point $(x, y)$ of edwards25519 (`edOnCurve`: coordinates below $p$ and $-x^2 + y^2 = 1 + d x^2 y^2$) with $x \ne 0$ and $y \ne 1$, the point $u = (1 + y)/(1 - y)$, $v = s\,u/x$ lies on curve25519 (`montOnCurve`: coordinates below $p$ and $v^2 = u^3 + 486662 u^2 + u$), and $s\,u/v = x$, $(u - 1)/(u + 1) = y$. Conversely, for every point $(u, v)$ of curve25519 with $v \ne 0$ and $u \ne p - 1$, the point $x = s\,u/v$, $y = (u - 1)/(u + 1)$ lies on edwards25519 with $x \ne 0$ and $y \ne 1$, and $(1 + y)/(1 - y) = u$, $s\,u/x = v$.
--   - **The base points correspond:** the base point $(X(P), Y(P))$ (`edBasepoint`) lies on edwards25519, and its $u$-coordinate $(1 + Y(P))/(1 - Y(P))$ (`edToMontU`) is $9$.
--
--   RFC 7748, §4.1: “This curve is birationally equivalent to a twisted Edwards curve -x^2 + y^2 = 1 + d*x^2*y^2, called "edwards25519"” […] “The birational maps are: (u, v) = ((1+y)/(1-y), sqrt(-486664)*u/x) (x, y) = (sqrt(-486664)*u/v, (u-1)/(u+1))”
-- source:
--   A. Langley, M. Hamburg and S. Turner, Elliptic Curves for Security, RFC 7748, January 2016, https://doi.org/10.17487/RFC7748, §4.1, the birational maps between curve25519 and edwards25519 (p. 1 of the excerpts)

import Mathlib
import Definitions.Def_X25519Dalek_Rfc7748

namespace X25519Dalek

theorem edwards25519_birational :
    (∃ s : Nat, s < p25519 ∧ fpSq s = fpNeg 486664) ∧
    (∀ s : Nat, fpSq s = fpNeg 486664 →
      (∀ x y : Nat, edOnCurve ⟨x, y⟩ = true → x ≠ 0 → y ≠ 1 →
        let u := fpMul (fpAdd 1 y) (fpInv (fpSub 1 y))
        let v := fpMul s (fpMul u (fpInv x))
        montOnCurve u v = true ∧
          fpMul s (fpMul u (fpInv v)) = x ∧ fpMul (fpSub u 1) (fpInv (fpAdd u 1)) = y) ∧
      (∀ u v : Nat, montOnCurve u v = true → v ≠ 0 → u ≠ p25519 - 1 →
        let x := fpMul s (fpMul u (fpInv v))
        let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
        edOnCurve ⟨x, y⟩ = true ∧ x ≠ 0 ∧ y ≠ 1 ∧
          fpMul (fpAdd 1 y) (fpInv (fpSub 1 y)) = u ∧ fpMul s (fpMul u (fpInv x)) = v)) ∧
    edOnCurve edBasepoint = true ∧ edToMontU edBasepoint = 9 := by
  sorry

end X25519Dalek

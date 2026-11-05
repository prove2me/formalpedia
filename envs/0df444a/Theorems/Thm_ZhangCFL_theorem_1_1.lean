-- Prove2me | Theorems.Thm_ZhangCFL_theorem_1_1
-- name    : ZhangCFL.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:56.097933+00:00
-- url     : https://prove2.me/theorems/920a99ed-4f23-4670-8deb-8f0b419e534c
-- title:
--   Theorem 1.1: full range of joint concavity/convexity of $\Psi_{p,q,s}(A,B)=\operatorname{Tr}(B^{q/2}K^*A^pKB^{q/2})^s$
-- statement:
--   Fix any invertible complex matrix $K$, and let $p,q,s$ be real numbers with $p\ge q$ and $s>0$. For positive definite matrices $A,B$ let
--
--   $$
--   \Psi_{p,q,s}(A,B) = \operatorname{Tr}\big(B^{q/2}K^*A^pKB^{q/2}\big)^s .
--   $$
--
--   Then $\Psi_{p,q,s}$, as a function of the pair $(A,B)$ on the convex set of pairs of positive definite matrices, is
--
--   1. jointly concave if $0\le q\le p\le 1$ and $0<s\le\frac1{p+q}$;
--   2. jointly convex if $-1\le q\le p\le 0$ and $s>0$;
--   3. jointly convex if $-1\le q\le 0$, $1\le p\le 2$, $(p,q)\neq(1,-1)$ and $s\ge\frac1{p+q}$.
--
--   By the symmetry of $\Psi_{p,q,s}$ the restriction $p\ge q$, $s>0$ loses no generality, and by Proposition 2.3 of the paper the ranges are sharp. Part (3) confirms, for invertible $K$, the Carlen–Frank–Lieb conjecture (the paper's Conjecture 2, stated for every $K$, follows by approximating $K$ with $K+\varepsilon I$, p.4), which contains the Audenaert–Datta conjecture behind the data processing inequality for the $\alpha$-$z$ Rényi relative entropies.
--
--   **Formalization Note** Joint concavity/convexity is `ConcaveOn`/`ConvexOn` on pairs of positive definite matrices. The bound $s\le\frac1{p+q}$ is written $s(p+q)\le 1$, and $s\ge\frac1{p+q}$ is written $s(p+q)\ge 1$.
--
--   Differences from the source:
--   - reading: s ≤ 1/(p+q) in (1) → s * (p + q) ≤ 1; reason: identical when p + q > 0; at p = q = 0, where 1/(p+q) is undefined on the page, it requires (1) for every s > 0, which is the non-vacuous reading (Ψ_{0,0,s} = Tr(K*K)^s is constant)
--   - encoding: s ≥ 1/(p+q) in (3) → 1 ≤ s * (p + q); reason: in (3) p ≥ 1 and q ≥ −1 with (p,q) ≠ (1,−1), so p + q > 0 and the two are equivalent
--   - encoding: Tr(B^{q/2}K*A^pKB^{q/2})^s → real part of Matrix.trace; reason: the matrix inside the trace is positive definite, so its trace is real
--   - encoding: operators on a finite-dimensional Hilbert space and invertible K → complex matrices indexed by a finite type, Matrix.PosDef and IsUnit K; reason: the same objects in a chosen basis
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, Theorem 1.1, p.3 (definition (1.1) p.1; proof p.10)

import Mathlib
import Definitions.Def_ZhangCFL_Psi
open scoped ComplexOrder

namespace ZhangCFL

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, Theorem 1.1, p.3: fix any invertible matrix `K`. Suppose that `p ≥ q` and
`s > 0`. Then `Ψ_{p,q,s}(A, B) = Tr(B^{q/2} K* A^p K B^{q/2})^s` (eq. (1.1)) is
(1) jointly concave if `0 ≤ q ≤ p ≤ 1` and `0 < s ≤ 1/(p+q)`;
(2) jointly convex if `−1 ≤ q ≤ p ≤ 0` and `s > 0`;
(3) jointly convex if `−1 ≤ q ≤ 0`, `1 ≤ p ≤ 2`, `(p, q) ≠ (1, −1)` and `s ≥ 1/(p+q)`.

**Formalization Note.** Joint convexity/concavity is `ConvexOn`/`ConcaveOn` over the convex set
of pairs `(A, B)` of positive definite matrices. `s ≤ 1/(p+q)` is written `s * (p + q) ≤ 1`:
the two agree when `p + q > 0`, and at `p = q = 0` (where `1/(p+q)` is undefined on the page)
the clause asks concavity for every `s > 0`, which holds since `Ψ_{0,0,s}` is constant. In (3)
`p + q > 0`, so `1 ≤ s * (p + q)` is `s ≥ 1/(p+q)`. The trace's real part is taken. -/
theorem theorem_1_1 {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (hK : IsUnit K) (p q s : ℝ) (hpq : q ≤ p) (hs : 0 < s) :
    (0 ≤ q → p ≤ 1 → s * (p + q) ≤ 1 →
      ConcaveOn ℝ {x : Matrix n n ℂ × Matrix n n ℂ | x.1.PosDef ∧ x.2.PosDef}
        (fun x => Psi p q s K x.1 x.2)) ∧
    (-1 ≤ q → p ≤ 0 →
      ConvexOn ℝ {x : Matrix n n ℂ × Matrix n n ℂ | x.1.PosDef ∧ x.2.PosDef}
        (fun x => Psi p q s K x.1 x.2)) ∧
    (-1 ≤ q → q ≤ 0 → 1 ≤ p → p ≤ 2 → (p, q) ≠ (1, -1) → 1 ≤ s * (p + q) →
      ConvexOn ℝ {x : Matrix n n ℂ × Matrix n n ℂ | x.1.PosDef ∧ x.2.PosDef}
        (fun x => Psi p q s K x.1 x.2)) := by sorry

end ZhangCFL

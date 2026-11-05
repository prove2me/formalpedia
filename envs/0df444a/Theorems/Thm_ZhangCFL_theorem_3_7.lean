-- Prove2me | Theorems.Thm_ZhangCFL_theorem_3_7
-- name    : ZhangCFL.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:52.4285+00:00
-- url     : https://prove2.me/theorems/ce3f40f0-ace8-4bc7-bd74-c1f09a21e889
-- title:
--   Theorem 3.7 (Epstein, Hiai, Carlen–Lieb): concavity/convexity of $\Upsilon_{p,1/p}$ and $\Upsilon_{p,s}$
-- statement:
--   Fix an invertible complex matrix $K$ and write $\Upsilon_{p,s}(A)=\operatorname{Tr}(K^*A^pK)^s$ for positive definite $A$. Then:
--
--   1. $\Upsilon_{p,1/p}$ is concave when $0<p\le 1$ (Epstein);
--   2. $\Upsilon_{p,s}$ is convex when $-1\le p<0$ and $0<s\le 1$ (Hiai);
--   3. $\Upsilon_{p,1/p}$ is convex when $1\le p\le 2$ (Carlen–Lieb).
--
--   Concavity and convexity are on the convex set of positive definite matrices. These three particular cases are what Step 2 of the paper reduces Theorem 3.5 to; Step 3 derives them from Lemma 3.1.
--
--   **Formalization Note** $\Upsilon_{p,s}$ is `ZhangCFL.Upsilon p s K`; $1/p$ is the real reciprocal, and $p\neq 0$ in (1) and (3).
--
--   Differences from the source:
--   - encoding: Tr(K*A^pK)^s → real part of Matrix.trace; reason: (K*A^pK)^s is positive definite, so its trace is real
--   - encoding: operators on a finite-dimensional Hilbert space H, P(H)^× and B(H)^× → complex matrices indexed by a finite type, Matrix.PosDef and IsUnit; reason: the same objects in a chosen basis
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, Theorem 3.7, p.11 (cited from [Eps73, Hia13, CL08]; proof from Lemma 3.1 pp.11–12)

import Mathlib
import Definitions.Def_ZhangCFL_Upsilon
open scoped ComplexOrder

namespace ZhangCFL

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, Theorem 3.7, p.11 ([Eps73, Hia13, CL08]): fix an invertible `K`; then
(1) `Υ_{p,1/p}` is concave when `0 < p ≤ 1` (Epstein);
(2) `Υ_{p,s}` is convex when `−1 ≤ p < 0` and `0 < s ≤ 1` (Hiai);
(3) `Υ_{p,1/p}` is convex when `1 ≤ p ≤ 2` (Carlen–Lieb),
where `Υ_{p,s}(A) = Tr(K* A^p K)^s` on positive definite `A`.

**Formalization Note.** Concavity/convexity is `ConcaveOn`/`ConvexOn` over the convex set of
positive definite matrices. `1 / p` is the real reciprocal; `p ≠ 0` in (1) and (3). -/
theorem theorem_3_7 {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (hK : IsUnit K) :
    (∀ p : ℝ, 0 < p → p ≤ 1 →
      ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef} (Upsilon p (1 / p) K)) ∧
    (∀ p s : ℝ, -1 ≤ p → p < 0 → 0 < s → s ≤ 1 →
      ConvexOn ℝ {A : Matrix n n ℂ | A.PosDef} (Upsilon p s K)) ∧
    (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
      ConvexOn ℝ {A : Matrix n n ℂ | A.PosDef} (Upsilon p (1 / p) K)) := by sorry

end ZhangCFL

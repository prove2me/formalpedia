-- Prove2me | Theorems.Thm_ZhangCFL_theorem_3_5
-- name    : ZhangCFL.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:53.276417+00:00
-- url     : https://prove2.me/theorems/55121500-62ee-4cca-82e7-463755b20a43
-- title:
--   Theorem 3.5 (Carlen–Frank–Lieb): concavity/convexity of $\Upsilon_{p,s}(A)=\operatorname{Tr}(K^*A^pK)^s$
-- statement:
--   Fix an invertible complex matrix $K$ and write $\Upsilon_{p,s}(A)=\operatorname{Tr}(K^*A^pK)^s$ for positive definite $A$. Then $\Upsilon_{p,s}$ is
--
--   1. concave if $0<p\le 1$ and $0<s\le \frac1p$;
--   2. convex if $-1\le p\le 0$ and $s>0$;
--   3. convex if $1\le p\le 2$ and $s\ge\frac1p$.
--
--   Concavity and convexity are on the convex set of positive definite matrices. This is the one-variable statement to which Step 1 of the paper reduces Theorem 1.1, via the variational formulas of Theorem 3.3 and Lemma 3.2.
--
--   **Formalization Note** $\Upsilon_{p,s}$ is `ZhangCFL.Upsilon p s K`; $1/p$ is the real reciprocal, and $p\neq 0$ in (1) and (3). The endpoint $p=0$ of (2), where $\Upsilon_{0,s}$ is constant, is included as on the page.
--
--   Differences from the source:
--   - encoding: Tr(K*A^pK)^s → real part of Matrix.trace; reason: (K*A^pK)^s is positive definite, so its trace is real
--   - encoding: operators on a finite-dimensional Hilbert space H, P(H)^× and B(H)^× → complex matrices indexed by a finite type, Matrix.PosDef and IsUnit; reason: the same objects in a chosen basis
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, Theorem 3.5, p.9 ([CFL18, Proposition 5]; proof from Theorem 3.7 p.11)

import Mathlib
import Definitions.Def_ZhangCFL_Upsilon
open scoped ComplexOrder

namespace ZhangCFL

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, Theorem 3.5, p.9 ([CFL18, Proposition 5]): for any invertible `K`,
`Υ_{p,s}(A) = Tr(K* A^p K)^s` is
(1) concave if `0 < p ≤ 1` and `0 < s ≤ 1/p`;
(2) convex if `−1 ≤ p ≤ 0` and `s > 0`;
(3) convex if `1 ≤ p ≤ 2` and `s ≥ 1/p`.

**Formalization Note.** Concavity/convexity is `ConcaveOn`/`ConvexOn` over the convex set of
positive definite matrices. `1 / p` is the real reciprocal; `p ≠ 0` in (1) and (3). -/
theorem theorem_3_5 {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (hK : IsUnit K) :
    (∀ p s : ℝ, 0 < p → p ≤ 1 → 0 < s → s ≤ 1 / p →
      ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef} (Upsilon p s K)) ∧
    (∀ p s : ℝ, -1 ≤ p → p ≤ 0 → 0 < s →
      ConvexOn ℝ {A : Matrix n n ℂ | A.PosDef} (Upsilon p s K)) ∧
    (∀ p s : ℝ, 1 ≤ p → p ≤ 2 → 1 / p ≤ s →
      ConvexOn ℝ {A : Matrix n n ℂ | A.PosDef} (Upsilon p s K)) := by sorry

end ZhangCFL

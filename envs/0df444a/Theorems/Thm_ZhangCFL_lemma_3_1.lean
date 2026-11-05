-- Prove2me | Theorems.Thm_ZhangCFL_lemma_3_1
-- name    : ZhangCFL.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:15.650667+00:00
-- url     : https://prove2.me/theorems/9f7faab2-b8ac-4ac0-9f04-c4606bbfb115
-- title:
--   Lemma 3.1 (Lieb, Ando): joint concavity/convexity of $\operatorname{Tr}K^*A^pKB^{1-p}$
-- statement:
--   Let $K$ be an invertible complex matrix. For positive definite matrices $A,B$ of the same size consider
--
--   $$
--   \Psi_{p,1-p,1}(A,B) = \operatorname{Tr}K^*A^pKB^{1-p}.
--   $$
--
--   Then:
--
--   1. if $0<p\le 1$, the map $(A,B)\mapsto \operatorname{Tr}K^*A^pKB^{1-p}$ is jointly concave on pairs of positive definite matrices (Lieb's concavity theorem);
--   2. if $-1\le p<0$, it is jointly convex there (Ando's convexity theorem).
--
--   These classical results are the base of the paper's reduction: Theorem 3.7, Theorem 3.5 and finally Theorem 1.1 are derived from them by the variational method. The paper cites them and does not prove them.
--
--   **Formalization Note** Joint concavity/convexity is `ConcaveOn`/`ConvexOn` over the convex set of pairs of positive definite matrices, matrices forming a real vector space. Powers are `OgawaNagaoka.matPow`.
--
--   Differences from the source:
--   - encoding: Tr K*A^pKB^{1−p} → real part of Matrix.trace; reason: the trace of a product of two positive semidefinite matrices is real, so the real part changes no value
--   - encoding: operators on a finite-dimensional Hilbert space H, P(H)^× and B(H)^× → complex matrices indexed by a finite type, Matrix.PosDef and IsUnit; reason: the same objects in a chosen basis
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, Lemma 3.1, p.7 (cited from [Lie73, And79])

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow
open scoped ComplexOrder

namespace ZhangCFL

open OgawaNagaoka

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, Lemma 3.1, p.7 (Lieb [Lie73], Ando [And79]; cited, not proved in the paper):
for any invertible `K`, the function `Ψ_{p,1−p,1}(A, B) = Tr K* A^p K B^{1−p}` on pairs of positive
definite matrices is (1) jointly concave if `0 < p ≤ 1`; (2) jointly convex if `−1 ≤ p < 0`.

**Formalization Note.** Powers are `OgawaNagaoka.matPow` (`cfc` with `Real.rpow`); joint
convexity/concavity is `ConvexOn`/`ConcaveOn` over the convex set of pairs `(A, B)` of positive
definite matrices, matrices being a real vector space through `ℂ`. The value is the real part of
the trace (the trace of a product of two positive semidefinite matrices is real). -/
theorem lemma_3_1 {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (hK : IsUnit K) (p : ℝ) :
    (0 < p → p ≤ 1 →
      ConcaveOn ℝ {x : Matrix n n ℂ × Matrix n n ℂ | x.1.PosDef ∧ x.2.PosDef}
        (fun x => (K.conjTranspose * matPow x.1 p * K * matPow x.2 (1 - p)).trace.re)) ∧
    (-1 ≤ p → p < 0 →
      ConvexOn ℝ {x : Matrix n n ℂ × Matrix n n ℂ | x.1.PosDef ∧ x.2.PosDef}
        (fun x => (K.conjTranspose * matPow x.1 p * K * matPow x.2 (1 - p)).trace.re)) := by sorry

end ZhangCFL

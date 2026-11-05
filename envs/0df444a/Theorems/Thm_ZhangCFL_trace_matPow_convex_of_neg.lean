-- Prove2me | Theorems.Thm_ZhangCFL_trace_matPow_convex_of_neg
-- name    : ZhangCFL.trace_matPow_convex_of_neg
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:18.017479+00:00
-- url     : https://prove2.me/theorems/d697c59c-fac3-4cf1-8da8-c5712f6ad325
-- title:
--   Proof of Theorem 3.7: $Z\mapsto\operatorname{Tr}Z^{r}$ is convex for $r<0$
-- statement:
--   Let $r<0$. Then the map
--
--   $$
--   Z \longmapsto \operatorname{Tr} Z^{r}
--   $$
--
--   is convex on the set of positive definite complex matrices of a fixed size.
--
--   The paper uses this in the proof of Theorem 3.7 (2) with the exponent $r=\frac{s(1-p)}{s-1}$, $0<s<1$, $-1\le p<0$, citing [Car10, Theorem 2.10] (the trace of a convex function of a matrix is convex); together with Ando's convexity (Lemma 3.1 (2)) and Lemma 3.2 (2) it gives the convexity of $\Upsilon_{p,s}$ for $0<s<1$.
--
--   **Formalization Note** Powers are `OgawaNagaoka.matPow`; the value is the real part of the trace.
--
--   Differences from the source:
--   - encoding: Z ↦ Tr Z^{s(1−p)/(s−1)} for 0 < s < 1 and −1 ≤ p < 0 → Z ↦ Tr Z^r for every r < 0; reason: as s ranges over (0,1) and p over [−1,0), the exponent s(1−p)/(s−1) takes exactly the values in (−∞,0)
--   - encoding: Tr → real part of Matrix.trace; reason: Z^r is positive definite, so its trace is real
--   - encoding: operators on a finite-dimensional Hilbert space H and P(H)^× → complex matrices indexed by a finite type and Matrix.PosDef; reason: the same objects in a chosen basis
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, proof of Theorem 3.7, p.11 ("Thus Z ↦ TrZ^{s(1−p)/(s−1)} is convex (see for example [Car10, Theorem 2.10])")

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow
open scoped ComplexOrder

namespace ZhangCFL

open OgawaNagaoka

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, proof of Theorem 3.7, p.11 ("the function t ↦ t^{s(1−p)/(s−1)} is convex.
Thus Z ↦ Tr Z^{s(1−p)/(s−1)} is convex (see for example [Car10, Theorem 2.10])"; cited, not
proved in the paper): for every real `r < 0`, the map `Z ↦ Tr Z^r` is convex on positive
definite matrices.

**Formalization Note.** The page uses the exponent `r = s(1−p)/(s−1)` with `0 < s < 1` and
`−1 ≤ p < 0`; these exponents fill all of `(−∞, 0)`, so "every `r < 0`" is the page's claim.
Powers are `OgawaNagaoka.matPow` (`cfc` with `Real.rpow`); the value is the real part of the
trace. -/
theorem trace_matPow_convex_of_neg {n : Type} [Fintype n] [DecidableEq n]
    (r : ℝ) (hr : r < 0) :
    ConvexOn ℝ {Z : Matrix n n ℂ | Z.PosDef} (fun Z => (matPow Z r).trace.re) := by sorry

end ZhangCFL

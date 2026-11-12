-- Prove2me | Theorems.Thm_ZhangCFL_psi_eq_trAbsPow
-- name    : ZhangCFL.psi_eq_trAbsPow
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:51:05.086437+00:00
-- url     : https://prove2.me/theorems/479022e9-b55a-4111-a450-bcfae39967fe
-- title:
--   Proof of Theorem 1.1: $\Psi_{p,q,s}(A,B)=\operatorname{Tr}|A^{p/2}KB^{q/2}|^{2s}$
-- statement:
--   Let $A,B$ be positive definite complex matrices of the same size, $K$ any square complex matrix of that size, and $p,q,s$ real numbers. Then
--
--   $$
--   \Psi_{p,q,s}(A,B) = \operatorname{Tr}\big(B^{q/2}K^*A^pKB^{q/2}\big)^s = \operatorname{Tr}\big|A^{p/2}KB^{q/2}\big|^{2s},
--   $$
--
--   where $\operatorname{Tr}|M|^r=\operatorname{Tr}(M^*M)^{r/2}$.
--
--   This identity opens the proof of Theorem 1.1: it writes $\Psi_{p,q,s}$ as $\operatorname{Tr}|XY|^{2s}$ with $X=A^{p/2}K$ and $Y=B^{q/2}$, so that the variational formulas (3.1) and (3.2) of Theorem 3.3 apply.
--
--   **Formalization Note** $\operatorname{Tr}|M|^r$ is `ZhangCFL.trAbsPow r M`.
--
--   Differences from the source:
--   - generalization: K invertible, p ≥ q and s > 0 (the setting of the proof of Theorem 1.1) → any matrix K and any real p, q, s; reason: the identity uses none of these hypotheses, and the page's setting is an instance
--   - encoding: Tr(B^{q/2}K*A^pKB^{q/2})^s and Tr|M|^{2s} → real part of Matrix.trace, through ZhangCFL.Psi and ZhangCFL.trAbsPow (2 * s) M = real part of Tr (M*M)^s; reason: |M| = (M*M)^{1/2} as on p.4; M*M is positive semidefinite, so the trace is real
--   - encoding: operators on a finite-dimensional Hilbert space H and P(H)^× → complex matrices indexed by a finite type and Matrix.PosDef; reason: the same objects in a chosen basis
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, proof of Theorem 1.1, first display, p.10

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow
import Definitions.Def_ZhangCFL_Psi
import Definitions.Def_ZhangCFL_trAbsPow
open scoped ComplexOrder

namespace ZhangCFL

open OgawaNagaoka

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, proof of Theorem 1.1, first display, p.10:
`Ψ_{p,q,s}(A, B) = Tr(B^{q/2} K* A^p K B^{q/2})^s = Tr|A^{p/2} K B^{q/2}|^{2s}`.

**Formalization Note.** Stated for positive definite `A, B` and every matrix `K` and real
`p, q, s` (the page is inside the proof of Theorem 1.1, where `K` is invertible, `p ≥ q`,
`s > 0`). `Tr|M|^r` is `ZhangCFL.trAbsPow r M = Tr (M* M)^{r/2}`. -/
theorem psi_eq_trAbsPow {n : Type} [Fintype n] [DecidableEq n]
    (p q s : ℝ) (K A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosDef) :
    Psi p q s K A B = trAbsPow (2 * s) (matPow A (p / 2) * K * matPow B (q / 2)) := by sorry

end ZhangCFL

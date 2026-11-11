-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_polynomial_tail
-- name    : ZigZagStrong.ZigZag.polynomial_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:33.391868+00:00
-- url     : https://prove2.me/theorems/8aa79c85-f334-42e6-b14d-2b89c28916f3
-- title:
--   Theorem 2.6 — coefficient-norm matrix-polynomial tail bound
-- statement:
--   There is an absolute positive constant $C$ such that the following holds uniformly over $r\ge2$, matrix size $D$, self-adjoint matrix polynomials $P$, every size $n$ and $0<\varepsilon<K$. Write $q=\deg P$, $K=\sum_w\|A_w\|$, let $u_n$ be the independent permutation tuple restricted to constants-perpendicular vectors, and let $u$ be the free regular tuple. Then
--   $$\Pr[\|P(u_n)\|\ge\|P(u)\|+\varepsilon]\le C\frac Dn\left(\frac{Kq\log r}{\varepsilon}\right)^8\log\frac{eK}{\varepsilon}.$$
--   This states the source coefficient-norm and epsilon range. The published full-C-star-norm input has a narrower range and does not replace this bridge.
--
--   Differences from the source:
--   - encoding: Polynomial degree q and coefficient matrix operator norms → Exact polynomial degree and Euclidean continuous-linear-map norms of coefficient matrices; reason: These compute the same quantities; the constant precedes every polynomial, dimension, size and tolerance.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Theorem 2.6, p. 9.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem polynomial_tail  : ∃ C : ℝ, 0 < C ∧
  ∀ r D : ℕ, 2 ≤ r → ∀ P : StrongConv.NCPoly D r, P.IsSelfAdjoint →
  ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ε < coefficientNorm P →
    StrongConv.uniformProb (fun σ : Fin r → Equiv.Perm (Fin n) =>
      ‖P.eval (StrongConv.sLimit r)‖ + ε ≤ ‖P.eval (StrongConv.sModel σ)‖) ≤
      C * ((D : ℝ) / n) * (coefficientNorm P * P.degree * Real.log r / ε)^8 *
        Real.log (Real.exp 1 * coefficientNorm P / ε) := by sorry

end ZigZagStrong.ZigZag

-- Prove2me | Theorems.Thm_syracuse_positive_affine_word_realization
-- name    : syracuse_positive_affine_word_realization
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-02T01:32:08.795259+00:00
-- url     : https://prove2.me/theorems/78b082d4-594c-4179-8e50-8e372a26c563
-- title:
--   Positive integral affine words realize exact Syracuse return words
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$ be the Syracuse map, and write $T^i$ for $i$-fold iteration. Let $w=(a_0,\ldots,a_{p-1})$ be a finite list of natural numbers with every entry strictly positive. Put $p=|w|$, $K=\sum_i a_i$, and $D=2^K-3^p$.
--
--   Use the existing canonical community affine constant $C(w)=\texttt{syracuseAffineConstant}(w)$, defined by $C([])=0$ and $C(a::u)=3^{|u|}+2^a C(u)$.
--
--   Assume the explicit arithmetic inequality $3^p<2^K$, and assume $D\mid C(w)$. Then there is a natural number $m>0$ such that
--
--   $$T^p(m)=m,\qquad \bigl(v_2(3T^i(m)+1)\bigr)_{0\le i<p}=w.$$
--
--   The proof supplies the canonical quotient $m=C(w)/D$. The strict gap excludes the empty list and makes the natural-number denominator positive. No actual cycle is assumed in order to obtain that gap or construct the return. The valuation list is exact and ordered, with every indexed position retained.
--
--   The supplied return period need not be least, and repeated states and repeated word blocks are allowed. No primitivity, least-period, low-mean, minimum-state, state bound, or period-cap hypothesis is imposed. This is an exact realization theorem conditional on divisibility, not a theorem proving divisibility or nondivisibility for all admissible words. It does not exclude the remaining low-mean primitive words, close the unbounded cycle tail, or establish Collatz convergence.
-- source:
--   Elementary finite affine-recursion and cyclic-rotation argument using the canonical community syracuseAffineConstant export from https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7 and the Syracuse definition https://prove2.me/theorems/2d5fcb43-85b2-4d75-beb8-3e236e66eac3 . Credits those existing definitions; the canonical constant is not redefined. The proof preserves the independently whole-source-reviewed affine-rotation and candidate-realization mathematical namespaces. No global mathematical novelty, universal nondivisibility, complete cycle exclusion, or Collatz convergence claim is made.

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_positive_affine_word_realization (w : List ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    ∃ m : ℕ, 0 < m ∧ syracuseStep^[w.length] m = m ∧
      List.ofFn (fun i : Fin w.length =>
        (3 * syracuseStep^[i.val] m + 1).factorization 2) = w := by sorry

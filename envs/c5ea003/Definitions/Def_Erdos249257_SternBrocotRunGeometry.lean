-- Prove2me | Definitions.Def_Erdos249257_SternBrocotRunGeometry
-- name    : Erdos249257_SternBrocotRunGeometry
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:43:46.575415+00:00
-- url     : https://prove2.me/theorems/bc3344d2-bf8c-4816-9db8-6ce5e0ec34db
-- title:
--   Left-right step type for Stern–Brocot paths
-- statement:
--   This bundle introduces the two-constructor inductive type LR, with left and right steps and decidable equality and printable representation. It does not retain Stern–Brocot theorems.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/SternBrocotRunGeometry.lean#L1-L518
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Stern--Brocot geometry after inducing parabolic runs

This file isolates the unconditional combinatorial core of the induced-run
coordinate for the positive primitive-pair mass

`∑_{a,b ≥ 1, Nat.Coprime a b} 2^{-(a+b)}`.

The existing `GcdMomentCalculus` module uses the same mediant children for its
Mersenne cylinder mass.  Here the observable is different: the height of the
literal primitive pair.  A word is stored newest run first, so its head acts
last.  This convention makes the continuant recurrence structural:

`(A,B) ↦ (n*A+B,A)`.

The first theorem is the exact Fibonacci floor.  A word with `r` nonempty
alternating runs has height at least `Nat.fib (r+3)`, with equality when every
run has length one.  The defect-sensitivity layer then expands the complete
positive continuant defect, identifies the one-site coefficient
`F_{i+2} F_{r-i+1}`, and proves the sharp global gain
`F_{r+1} * ∑ eᵢ`.  The final section records the companion arithmetic
knife-edge: the sum of the natural Fibonacci run exponents is exactly two less
than the same Fibonacci height scale.

Nothing here proves irrationality of Erdős #249.  In particular, this module
does not assert that the analytic run tail survives denominator clearing.
-/

namespace SternBrocotRunGeometry

/-! ## The literal mediant tree -/

/-- The two Stern--Brocot mediant moves. -/
inductive LR
  | left
  | right
  deriving DecidableEq, Repr

















/-! ## Exact run encoding -/

















/-! ## Fibonacci pressure -/











/-! ## Exact defect sensitivity away from the Fibonacci spine -/



































/-! ## The first two analytic run layers -/









/-! ## The natural denominator exponent is at the Fibonacci knife-edge -/





-- Axiom audit: the induced-run geometry is foundational only.

end SternBrocotRunGeometry



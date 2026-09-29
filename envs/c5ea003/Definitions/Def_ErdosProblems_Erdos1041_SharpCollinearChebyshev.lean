-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
-- name    : ErdosProblems_Erdos1041_SharpCollinearChebyshev
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T03:41:53.098246+00:00
-- url     : https://prove2.me/theorems/808e92db-c9a5-443a-8e1f-4f28e4facba5
-- title:
--   Scaled Chebyshev comparator and sharp normalized height
-- statement:
--   For integer degree $n$, this bundle defines $r_n=\cos(\pi/(2n))$, the endpoint-normalized monic scaled Chebyshev polynomial, and its comparison height $C_n=|2^{-(n-1)}r_n^{-n}|$. For $n\ge2$, later theorems establish that this polynomial is monic of degree $n$ and that $C_n=[2^{n-1}\cos^n(\pi/(2n))]^{-1}$. These definitions support the alternation comparison; the bundle itself makes no theorem or proof-status claim.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean#L33-L45

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

namespace ErdosProblems.Erdos1041.SharpCollinearAlternation
end ErdosProblems.Erdos1041.SharpCollinearAlternation

/-!
# The sharp Chebyshev comparator for collinear Erdos #1041

For degree `n`, put `r = cos (pi / (2n))`.  The polynomial

`T_n(r X) / (2^(n-1) r^n)`

is monic, vanishes at `-1` and `1`, and has absolute value at most

`1 / (2^(n-1) r^n)`

on `[-1,1]`.  Combining these facts with the constrained alternation theorem
gives the sharp upper bound for one of the alternating interior peaks of any
monic comparison polynomial with the same endpoint zeros.
-/

namespace ErdosProblems.Erdos1041.SharpCollinearChebyshev

open Set
open Polynomial

open ErdosProblems.Erdos1041.SharpCollinearAlternation

/-- The scale that sends the two outermost roots of `T_n` to `-1` and `1`. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))

/-- The endpoint-normalised monic Chebyshev comparison polynomial. -/
noncomputable def monicScaledChebyshev (n : ℕ) : ℝ[X] :=
  C (((2 : ℝ) ^ (n - 1))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹

/-- The sharp normalised height.  A later algebraic simplification rewrites
this as `1 / (2^(n-1) * cos(pi/(2n))^n)`. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|



















end ErdosProblems.Erdos1041.SharpCollinearChebyshev



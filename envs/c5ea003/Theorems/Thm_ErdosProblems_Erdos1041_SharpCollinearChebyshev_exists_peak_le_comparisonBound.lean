-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_exists_peak_le_comparisonBound
-- name    : ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T03:44:59.822082+00:00
-- url     : https://prove2.me/theorems/a100a576-459f-4032-bed9-ba95bf5c9ffa
-- title:
--   A Chebyshev bound at one alternating peak
-- statement:
--   Let $p$ be monic of degree $m+2$, vanish at $-1$ and $1$, and have alternating signs at $m+1$ strictly ordered points inside $(-1,1)$. Then at least one of those points has $|p|\le C_{m+2}$, where $C_n=[2^{n-1}\cos^n(\pi/(2n))]^{-1}$. This specializes the abstract comparison principle to the scaled Chebyshev comparator.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean#L130-L149

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
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


open Set
open Polynomial

open ErdosProblems.Erdos1041.SharpCollinearAlternation

open ErdosProblems.Erdos1041.SharpCollinearChebyshev

theorem ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by sorry

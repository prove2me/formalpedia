-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ
-- name    : ErdosProblems.Erdos1049.gaussBinom_succ
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:19:13.407753+00:00
-- url     : https://prove2.me/theorems/866240c8-6e31-4366-81e8-baa316060d13
-- title:
--   Gauss binom succ
-- statement:
--   The Gaussian binomial coefficient at (n+1,k+1) obeys its stated two-term recurrence, with the second term zero outside k≤n.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QBinomialUnitIdentity.lean#L86-L89
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: finite q-binomial algebra for the 2004 small-p unit

Zudilin, Acta Arith. 111 (2004), displays (8)–(11).  After the published
integrality exponent `M` is removed, the second source coefficient is a
unit at `p = 0`.  The new algebra is the finite q-binomial theorem, the
vanishing range for exponents that hit `1`, and the constant term of
`(q^α; q)_n` for `α ≥ 1`.  This module Lean-checks those identities.  It
does not construct the source sums `A(p), B(p)`, does not prove
irrationality of `F(3/2)`, and is not the 2016 Hankel family.

The Gaussian binomial uses the same Pascal recurrence as
`AdelicHeightBridge.zudilinQBinomialPS`, as a ring element rather than a
power series.
-/

open scoped BigOperators
open Finset Polynomial


variable {R : Type*} [CommRing R]

/-! ## q-Pochhammer and Gaussian binomials -/

open ErdosProblems.Erdos1049

theorem ErdosProblems.Erdos1049.gaussBinom_succ (q : R) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) =
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0 := by sorry

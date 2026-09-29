-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_mul_qPochhammer_qPochhammer
-- name    : ErdosProblems.Erdos1049.gaussBinom_mul_qPochhammer_qPochhammer
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:48:19.042487+00:00
-- url     : https://prove2.me/theorems/c57931b3-c35b-4bf6-bb1e-27a85075151d
-- title:
--   Gauss binom mul q pochhammer q pochhammer
-- statement:
--   For k≤n, the Gaussian binomial coefficient times its two finite Pochhammer denominators equals the numerator (q;q)_n.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QBinomialUnitIdentity.lean#L287-L350
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































/-! ## Finite q-binomial theorem -/













/-! ## Splitting `(q;q)_{m+k}` and the constant term at the small-p endpoint -/









/-! ## Gaussian binomial times `(q;q)_k` -/

open ErdosProblems.Erdos1049

theorem ErdosProblems.Erdos1049.gaussBinom_mul_qPochhammer_qPochhammer (q : R) :
    ∀ n k, k ≤ n →
      gaussBinom q n k * qPochhammer q q k * qPochhammer q q (n - k) =
        qPochhammer q q n
  := by sorry

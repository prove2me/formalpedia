-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
-- name    : ErdosProblems.Erdos1049.qPochhammer_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:22:26.698129+00:00
-- url     : https://prove2.me/theorems/2d8fa970-145b-408b-9ff6-71c1d0fec805
-- title:
--   Q pochhammer zero
-- statement:
--   The empty finite q-Pochhammer product is one.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QBinomialUnitIdentity.lean#L38-L38
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

@[simp] theorem ErdosProblems.Erdos1049.qPochhammer_zero (q z : R) : qPochhammer q z 0 = 1 := by sorry

-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
-- name    : ErdosProblems_Erdos1049_QBinomialUnitIdentity
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:45:19.888727+00:00
-- url     : https://prove2.me/theorems/78b1f744-4ea1-4dab-b4e0-50faace034e4
-- title:
--   Erdős #1049: finite q-binomial algebra for the 2004 small-p unit
-- statement:
--   Pascal-recursive Gaussian coefficients support the finite q-binomial theorem; its vanishing and constant-term cases prove the small-p unit in the 2004 coefficient. The submitted module contains the source declarations qPochhammer, qPochhammer_zero, qPochhammer_succ, qPochhammer_eq_zero_of_exists, qPochhammer_one, among others. Source topic: Erdős #1049: finite q-binomial algebra for the 2004 small-p unit.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QBinomialUnitIdentity.lean#L33-L477
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

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

namespace ErdosProblems.Erdos1049

variable {R : Type*} [CommRing R]

/-! ## q-Pochhammer and Gaussian binomials -/

/-- Finite q-Pochhammer `(z; q)_n = ∏_{i=0}^{n-1} (1 - z q^i)`. -/
def qPochhammer (q z : R) : ℕ → R
  | 0 => 1
  | n + 1 => qPochhammer q z n * (1 - z * q ^ n)











/-- Gaussian binomial by the Pascal recurrence
`[n+1 choose k+1]_q = [n choose k+1]_q + q^{n-k} [n choose k]_q`. -/
def gaussBinom (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0

















/-! ## Finite q-binomial theorem -/

/-- The summand of `(z; q)_n = ∑_k [n choose k]_q (-1)^k q^{binom k 2} z^k`. -/
def qBinomialTerm (q z : R) (n k : ℕ) : R :=
  gaussBinom q n k * (-1 : R) ^ k * q ^ k.choose 2 * z ^ k











/-! ## Splitting `(q;q)_{m+k}` and the constant term at the small-p endpoint -/









/-! ## Gaussian binomial times `(q;q)_k` -/













/-! ## Source identity (2.3), cleared of `(q;q)_{a-1}` -/





end ErdosProblems.Erdos1049



-- Prove2me | Definitions.Def_mme_dyadic_log_interval
-- name    : mme_dyadic_log_interval
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-30T08:16:33.056884+00:00
-- url     : https://prove2.me/theorems/2bb95a42-99d0-46eb-bc84-6a64e31bdd86
-- title:
--   Fixed-scale integer logarithm and entropy evaluators
-- statement:
--   Fix a positive integer scale $S$, usually a power of two. An interval with integer endpoints $L,U$ represents
--
--   $$L\le Sx\le U.$$
--
--   The operations add intervals, multiply nonnegative intervals with outward integer rounding, and divide by positive natural numbers with outward rounding. A recurrence evaluates the finite series for $\log((1+t)/(1-t))$ when $0\le t\le1/3$, including an upper estimate for its tail.
--
--   For positive integers $p,d$ and a supplied shift $k$ satisfying $d\le p2^k\le2d$, the signed evaluator bounds $\log(p/d)$ by undoing the power-of-two scaling. Its entire computation uses natural numbers and integers; correctness is a separate theorem.
--
--   A table consists of pairs $(p_i,k_i)$ with common denominator $d$. The entropy evaluator returns endpoints at scale $Sd$ for $\sum_i -(p_i/d)\log(p_i/d)$. Zero entries contribute exactly zero. The range check validates the shifts for nonzero entries; it does not assert that the counts sum to $d$.
--
--   This is supporting numerical-verification data for the level-four matrix-multiplication certificate. It contains no level-four witness and asserts no matrix-multiplication exponent bound.
-- source:
--   Supporting numerical-verification construction for Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, arXiv:2608.16884v1, Section 4, https://arxiv.org/html/2608.16884v1#S4. The fixed-scale evaluator is an auxiliary construction, not a claim stated in that paper. Its analytic foundation is Mathlib 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e, Analysis/SpecialFunctions/Log/Deriv.lean, Real.sum_range_le_log_div and Real.log_div_le_sum_range_add.

import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace MME.DyadicLog

/-- Integer endpoints at a common positive scale. -/
structure Interval where
  lo : ℕ
  hi : ℕ
  deriving Repr, DecidableEq

def Interval.Valid (S : ℕ) (a : Interval) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (S : ℝ) * x ∧ (S : ℝ) * x ≤ (a.hi : ℝ)

def zero : Interval := ⟨0, 0⟩

def add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Round down the lower product and strictly round up the upper product. -/
def mul (S : ℕ) (a b : Interval) : Interval :=
  ⟨a.lo * b.lo / S, a.hi * b.hi / S + 1⟩

def divNat (d : ℕ) (a : Interval) : Interval := ⟨a.lo / d, a.hi / d + 1⟩

def ratio (S p d : ℕ) : Interval := ⟨S * p / d, S * p / d + 1⟩

/-- At iteration n, power encloses t^(2*n+1) and total encloses the first
n terms of the atanh series. All computations use natural-number arithmetic. -/
structure State where
  power : Interval
  total : Interval
  deriving Repr, DecidableEq

def series (S : ℕ) (t : Interval) : ℕ → State
  | 0 => ⟨t, zero⟩
  | n + 1 =>
      let prev := series S t n
      ⟨mul S prev.power (mul S t t),
        add prev.total (divNat (2 * n + 1) prev.power)⟩

/-- For 0 ≤ t ≤ 1/3, 9/8 bounds the geometric remainder factor.
The result bounds log((1+t)/(1-t)) at the same integer scale. -/
def logInterval (S : ℕ) (t : Interval) (n : ℕ) : Interval :=
  let state := series S t n
  ⟨2 * state.total.lo,
    2 * (state.total.hi + (9 * state.power.hi / 8 + 1))⟩

/-- Input p/d in [1,2]. Only the initial conversion handles the input's
denominator; the series itself uses the fixed scale S. -/
def unitLog (S p d n : ℕ) : Interval :=
  logInterval S (ratio S (p - d) (p + d)) n

structure SignedInterval where
  lo : ℤ
  hi : ℤ
  deriving Repr, DecidableEq

def SignedInterval.Valid (S : ℕ) (a : SignedInterval) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (S : ℝ) * x ∧ (S : ℝ) * x ≤ (a.hi : ℝ)

/-- Range reduction for positive p/d: normalize p*2^k/d into [1,2],
then subtract k certified copies of log 2. -/
def scaledLog (S p d k n : ℕ) : SignedInterval :=
  let a := unitLog S (p * 2 ^ k) d n
  let b := unitLog S 2 1 n
  ⟨(a.lo : ℤ) - (k : ℤ) * (b.hi : ℤ),
    (a.hi : ℤ) - (k : ℤ) * (b.lo : ℤ)⟩

/-- A cell contributes -(p/d) log(p/d). Endpoints use scale S*d.
The zero-probability case is handled exactly, without evaluating log 0. -/
def entropyCell (S p d k n : ℕ) : SignedInterval :=
  if p = 0 then ⟨0, 0⟩ else
    let a := scaledLog S p d k n
    ⟨-(p : ℤ) * a.hi, -(p : ℤ) * a.lo⟩

/-- Each entry is (integer count, binary range-reduction shift). -/
def entropyInterval (S d n : ℕ) : List (ℕ × ℕ) → SignedInterval
  | [] => ⟨0, 0⟩
  | (p, k) :: rest =>
      let a := entropyCell S p d k n
      let b := entropyInterval S d n rest
      ⟨a.lo + b.lo, a.hi + b.hi⟩

def rangeReductionCheck (d : ℕ) (cells : List (ℕ × ℕ)) : Bool :=
  cells.all (fun cell ↦ decide (cell.1 = 0 ∨
    (d ≤ cell.1 * 2 ^ cell.2 ∧ cell.1 * 2 ^ cell.2 ≤ 2 * d)))

end MME.DyadicLog



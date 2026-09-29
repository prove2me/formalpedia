-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR21_TwoPrimeSums
-- name    : ErdosProblems_Erdos269_PaperCompleteR21_TwoPrimeSums
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:13:22.25798+00:00
-- url     : https://prove2.me/theorems/9898917c-d549-49d9-b632-375d9b30830a
-- title:
--   TwoPrimeSums
-- statement:
--   Defines positive two-prime smooth numbers, their running height and LCM, exponent recoding maps, distinct and repeated sums, jump terms, and the Hecke–Mahler series interface. The Bugeaud–Laurent transcendence input is explicitly named and retains its hypotheses.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L1-L951
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7AnalyticInterfaces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: both two-prime running-LCM sums

This file transcribes the two-prime objects of the short paper's
`res:two-prime-transcendence` and of the long paper's `long269:res:lead-two-prime`
and proves everything those statements assert except one external value theorem.

* `runningLcm p q x` is the literal least common multiple of the `{p,q}`-smooth
  numbers not exceeding `x`; `runningLcm_eq_twoPrimeHeight` identifies it with the
  product of the two maximal pure prime powers.
* `repeatedSum p q` is `R_{p,q}`: the reciprocal running LCM summed at every
  positive `{p,q}`-smooth integer.  `distinctSum p q` is `D_{p,q}`: each distinct
  running LCM counted once.
* `two_prime_affine_and_quadratic` proves the paper's displayed identities
  `eq:two-prime-affine`, with `A` the paper's boundary value
  `ErdosProblems.Erdos269.PaperR7.twoPrimeHeckeValue`.
* `two_prime_sums_transcendental` and `two_prime_transcendence` conclude that both
  values are transcendental.

The only undischarged input is `BugeaudLaurentTranscendence`, the theorem of
Bugeaud and Laurent (Theorem 1.1) in the case `ρ = 0` due to Loxton and van der
Poorten (Theorem 8, p. 40), that the Hecke--Mahler series takes transcendental
values.  It is carried as one explicit named hypothesis, stated in the generality
in which the paper cites it; all of its side conditions for the pair `(1/p, 1/q)`,
including irrationality of the slope `θ = log p / log q`, are proved here.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR21

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## The `{p,q}`-smooth numbers and their running least common multiple -/

/-- The positive `{p,q}`-smooth integers. -/
def SmoothSet (p q : ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∃ i j : ℕ, n = p ^ i * q ^ j}

/-- The product of the two maximal pure prime powers not exceeding `x`. -/
def twoPrimeHeight (p q x : ℕ) : ℕ := p ^ Nat.log p x * q ^ Nat.log q x

/-- The exponent pairs of the actual `{p,q}`-smooth prefix up to `x`. -/
def smoothPrefixPairs (p q x : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (Nat.log p x + 1)) ×ˢ (Finset.range (Nat.log q x + 1))).filter
    fun e => p ^ e.1 * q ^ e.2 ≤ x)

/-- The literal running least common multiple of the `{p,q}`-smooth numbers `≤ x`. -/
def runningLcm (p q x : ℕ) : ℕ :=
  (smoothPrefixPairs p q x).lcm fun e => p ^ e.1 * q ^ e.2







/-! ## Integer logarithms at smooth points -/







/-- `m_n = ⌊n θ⌋`: the exponent of the largest power of `q` not exceeding `p ^ n`. -/
def qExp (p q n : ℕ) : ℕ := Nat.log q (p ^ n)

/-- `⌊j / θ⌋`: the exponent of the largest power of `p` not exceeding `q ^ j`. -/
def pExp (p q j : ℕ) : ℕ := Nat.log p (q ^ j)















/-! ## The exact combinatorics of the jump indices -/











/-! ## Unique factorisation of the smooth monoid -/







/-! ## The two sums of the paper -/

/-- `R_{p,q}`: the reciprocal running LCM summed at every positive
`{p,q}`-smooth integer. -/
def repeatedSum (p q : ℕ) : ℝ :=
  ∑' n : SmoothSet p q, ((runningLcm p q (n : ℕ) : ℝ))⁻¹

/-- The distinct values taken by the running LCM on the positive smooth integers. -/
def runningLcmValues (p q : ℕ) : Set ℕ := (runningLcm p q) '' SmoothSet p q

/-- `D_{p,q}`: each distinct running LCM counted once. -/
def distinctSum (p q : ℕ) : ℝ :=
  ∑' H : runningLcmValues p q, (((H : ℕ) : ℝ))⁻¹

/-! ## The two component series -/

/-- The reciprocal running value at the pure power `p ^ n`, that is `x^n y^{m_n}`. -/
def aTerm (p q n : ℕ) : ℝ := ((p : ℝ)⁻¹) ^ n * ((q : ℝ)⁻¹) ^ qExp p q n

/-- The reciprocal running value at the pure power `q ^ j`, that is
`x^{⌊j/θ⌋} y^j`. -/
def cTerm (p q j : ℕ) : ℝ := ((p : ℝ)⁻¹) ^ pExp p q j * ((q : ℝ)⁻¹) ^ j























/-! ## `R = A (1 + B)` -/





/-! ## `D = A + B` -/

/-- The running value at the `a`-th pure power of `p`. -/
def jumpLeft (p q a : ℕ) : ℕ := twoPrimeHeight p q (p ^ a)

/-- The running value at the `(b+1)`-st pure power of `q`. -/
def jumpRight (p q b : ℕ) : ℕ := twoPrimeHeight p q (q ^ (b + 1))















/-! ## The telescoping identity `A - 1 - x A = x (y-1) B / y` -/

/-- The shifted series `x^n y^{m_{n+1}}`. -/
def sTerm (p q n : ℕ) : ℝ := ((p : ℝ)⁻¹) ^ n * ((q : ℝ)⁻¹) ^ qExp p q (n + 1)

/-- The telescoping difference `x^n (y^{m_n} - y^{m_{n+1}})`. -/
def dTerm (p q n : ℕ) : ℝ := aTerm p q n - sTerm p q n











/-! ## The Hecke--Mahler boundary value -/

/-- The Hecke--Mahler series `F_θ(β,α) = ∑_{n≥1} ∑_{k=1}^{⌊nθ⌋} β^n α^k`.  The
outer index runs over all `n ≥ 0`; the inner sum is empty at `n = 0`. -/
def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k

/-- Bugeaud and Laurent, Theorem 1.1, in the case `ρ = 0` due to Loxton and van der
Poorten, Theorem 8, p. 40: the Hecke--Mahler series takes transcendental values at
nonzero algebraic arguments inside the stated region.  This is the one external
input of the two-prime theorem. -/
def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)









/-! ## Irrationality of the slope -/



/-! ## Transcendence -/







/-! ## The paper's theorems -/












end

end ErdosProblems.Erdos269.PaperCompleteR21



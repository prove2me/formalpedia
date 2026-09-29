-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
-- name    : ErdosProblems_Erdos243_ReciprocalTailRigidity
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:26:40.259342+00:00
-- url     : https://prove2.me/theorems/a915de73-98a4-40cd-a614-513b5e0b3c44
-- title:
--   Exact reciprocal-tail state and centered error
-- statement:
--   Defines the integer Sylvester next term a²−a+1, denominator and tail-state transitions, centered error E=D−(a−1)C, and the Sylvester defect. Included proofs establish C_(n+1)=C_n−E_n and the transition to the next digit when TWO consecutive centered errors E_n=E_(n+1)=0 and the next tail state is nonzero. A single zero error alone does not yield the full Sylvester transition; eventual zero is the conclusion of separate rigidity theorems.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1-L2353
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_ReciprocalTailRigidity is the versioned native alias of original module ErdosProblems.Erdos243.ReciprocalTailRigidity.

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős #243: reciprocal-tail rigidity

This module owns the exact centered integer dynamics behind the rational case.
It proves the algebraic defect identity and the well-founded stabilization step:
if the centered errors are eventually nonnegative, the natural tail state is
nonincreasing and the errors eventually vanish.  It excludes both constant
negative centered states and, in the natural tail regime, every positive
eventually periodic negative-state magnitude.  It also proves the arithmetic
core of the stronger bounded-aperiodic route: an exact reduced tail tending to
infinity cannot have bounded upward increments.  That proof combines exact
coprimality, whole-modulus avoidance, a shifted CRT barrier, and first crossing.

It does not settle the unrestricted problem, whose live obstruction is an
integer centered state with cofinally unbounded negative excursions.  The full
bounded-negative-part regime is closed below without a periodicity hypothesis.
For the remaining branch, dynamic gcd reduction is also made exact: every gcd
growth factor is paid for by old-prime overlap.  Normalized centered-state
vanishing now yields local near-unit tail growth, explicit subexponential tail
growth, and hence sublinear strict gcd growth through the finite `2^r` budget.
The residual is to turn sparse old-prime reuse into a contradiction.
-/

namespace ErdosProblems.Erdos243

/-- The Sylvester successor `a² - a + 1`, expressed in a ring. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. -/
def nextDenState (a D : ℤ) : ℤ :=
  a * D

/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. -/
def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D

/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. -/
def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-- The next denominator defect from the Sylvester step. -/
def sylvesterDefect (a aNext : ℤ) : ℤ :=
  aNext - sylvesterNext a

/-- The tail update is exactly `Cₙ₊₁ = Cₙ - Eₙ`. -/
theorem nextTailState_eq_sub_centered (a D C : ℤ) :
    nextTailState a D C = C - centeredState a D C := by
  simp [nextTailState, centeredState]
  ring

/-! The entire integer-state system is equivariant under a common scale.  This
removes a large family of duplicate constant-negative-state searches. -/







/-! ## Excluding the normalized constant-negative orbit

If `Eₙ = -1` and `C₀ = 1`, then `Cₙ = n + 1` and the centered-state
identity becomes

`Dₙ + 1 = (n + 1) (aₙ - 1)`.

On the other hand, `Dₙ₊₁ = aₙ Dₙ` makes every `Dₙ` with `n ≥ 1`
divisible by `a₀`.  Evaluating the displayed identity at `n = a₀ - 1`
would make both `Dₙ` and `Dₙ + 1` divisible by `a₀`, impossible for
`a₀ ≥ 2`.  This consumes the exact multiplicative denominator update above
and closes the normalized branch explored by `FiniteHorizonResidue`.
-/









/-! ## Excluding phase-primitive periodic negative magnitudes

The constant-negative argument has a periodic analogue.  Write `eₙ = -Eₙ`
for a positive negative-state magnitude, so that `Cₙ₊₁ = Cₙ + eₙ` and

`Dₙ + eₙ = (aₙ - 1) Cₙ`.

If a divisor `p` occurs in two distinct multiplier states `aⱼ` and `aₖ`, then
the first occurrence puts `p` into `Dₖ`, while the second occurrence forces
`p ∣ Cₖ₊₁`.  From there `p` divides every later `D`, `C`, and `e`.
When `e` is periodic and `C` has a fixed positive drift over one period, any
prime divisor of that drift propagates back to all phases.  A finite-prime
pigeonhole argument therefore excludes a phase-primitive periodic orbit.
-/



















/-! ## The bounded aperiodic route: a CRT barrier

Periodicity is not needed once the reduced exact tail supplies infinitely many
pairwise-coprime moduli which every later numerator must avoid.  The finite
producer below places a consecutive forbidden block past any prescribed
height. -/















/-! The remaining bounded-negative wrapper needs the tail gcd to stabilise.
The next lemmas kernel-check that exact arithmetic reduction. -/

/-! ## Dynamic cancellation and the gcd-growth budget

Before the tail gcd stabilises, reduction at consecutive indices introduces a
growth factor `h`.  The exact normalized step below shows that `h` is paid for
by overlap between the current multiplier and the reduced denominator.  The
finite counting lemmas then quantify how expensive strict gcd growth is.
-/























































/-- Exact defect equation from the packet:
`Δₙ Cₙ₊₁ = aₙ² Eₙ - Eₙ₊₁`. -/
theorem sylvesterDefect_mul_nextTailState
    (a aNext D C : ℤ) :
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := by
  simp [sylvesterDefect, sylvesterNext, nextTailState, nextDenState,
    centeredState]
  ring

/-- If two consecutive centered errors vanish and the next tail state is
nonzero, the defect identity forces the original denominator sequence to take
the exact Sylvester step. -/
theorem sylvesterNext_eq_of_centered_zero
    (a aNext D C : ℤ)
    (hCnext : nextTailState a D C ≠ 0)
    (hE : centeredState a D C = 0)
    (hEnext :
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0) :
    aNext = sylvesterNext a := by
  have hdefect := sylvesterDefect_mul_nextTailState a aNext D C
  rw [hE, hEnext] at hdefect
  simp only [mul_zero, sub_zero] at hdefect
  have hzero : sylvesterDefect a aNext = 0 :=
    (mul_eq_zero.mp hdefect).resolve_right hCnext
  rw [sylvesterDefect] at hzero
  exact sub_eq_zero.mp hzero

/-- Along an exact product-cleared tail orbit, eventual vanishing of the
centered state and eventual nonvanishing of the next tail force the exact
Sylvester recurrence from some index onward. -/
theorem sylvesterNext_eventually_of_centered_zero
    (a D C : ℕ → ℤ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) = nextTailState (a n) (D n) (C n))
    (hE : ∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0)
    (hCne : ∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  obtain ⟨NE, hE⟩ := hE
  obtain ⟨NC, hCne⟩ := hCne
  refine ⟨max NE NC, fun n hn ↦ ?_⟩
  have hnE : NE ≤ n := (Nat.le_max_left NE NC).trans hn
  have hnC : NC ≤ n := (Nat.le_max_right NE NC).trans hn
  apply sylvesterNext_eq_of_centered_zero (a n) (a (n + 1)) (D n) (C n)
  · rw [← hC n]
    exact hCne n hnC
  · exact hE n hnE
  · rw [← hD n, ← hC n]
    exact hE (n + 1) (hnE.trans (Nat.le_succ n))





/-! ## Bounded negative part: the signed wrapper

The preceding CRT theorem excludes cofinally many bounded negative errors once
their nonzero magnitudes vanish relative to the tail.  The final wrapper has
two additional ingredients.  First, the exact defect identity makes zero
absorbing as soon as the centered representative satisfies `|Eₙ| < Cₙ`.
Second, failure of cofinal negativity leaves an eventually nonnegative natural
tail, so `centeredState_eventually_zero` applies.
-/

/-- The natural product-cleared recurrence realizes the integer tail update
used by `nextTailState`. -/
theorem natTail_eq_nextTailState
    (a C D : ℕ → ℕ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n) (n : ℕ) :
    (C (n + 1) : ℤ) =
      nextTailState (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
  have hCast := congrArg (fun x : ℕ ↦ (x : ℤ)) (hC n)
  simp only [Nat.cast_add, Nat.cast_mul] at hCast
  simp only [nextTailState]
  omega

/-- The natural denominator recurrence realizes `nextDenState` over the
integers. -/
theorem natDen_eq_nextDenState
    (a D : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n) (n : ℕ) :
    (D (n + 1) : ℤ) = nextDenState (a n : ℤ) (D n : ℤ) := by
  have hCast := congrArg (fun x : ℕ ↦ (x : ℤ)) (hD n)
  simpa only [Nat.cast_mul, nextDenState] using hCast

/-- Along an exact natural orbit, the signed centered state gives the integer
tail identity `Cₙ₊₁ = Cₙ - Eₙ`. -/
theorem natTail_eq_sub_centeredState
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) :
    (C (n + 1) : ℤ) = (C n : ℤ) - E n := by
  rw [natTail_eq_nextTailState a C D hC n,
    nextTailState_eq_sub_centered, ← hE n]



























end ErdosProblems.Erdos243



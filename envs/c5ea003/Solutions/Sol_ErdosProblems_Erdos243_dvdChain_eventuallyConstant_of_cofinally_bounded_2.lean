-- Prove2me | solution 2 for ErdosProblems.Erdos243.dvdChain_eventuallyConstant_of_cofinally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:57:39.73308+00:00
-- url     : https://prove2.me/submissions/432fd70c-3e2a-4123-a49f-41cfecbf53d3

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
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
end ErdosProblems.Erdos243

open ErdosProblems in
open ErdosProblems.Erdos243 in
theorem solution
    (G : ℕ → ℕ) (B : ℕ)
    (hpos : ∀ n, 0 < G n)
    (hchain : ∀ n, G n ∣ G (n + 1))
    (hcofinal : ∀ n, ∃ t, n ≤ t ∧ G t ≤ B) :
    ∃ N, ∀ n, N ≤ n → G n = G N := by
  classical
  have hmonoStep : ∀ n, G n ≤ G (n + 1) := by
    intro n
    exact Nat.le_of_dvd (hpos (n + 1)) (hchain n)
  have hmono : Monotone G := monotone_nat_of_le_succ hmonoStep
  have hbound : ∀ n, G n ≤ B := by
    intro n
    obtain ⟨t, hnt, htB⟩ := hcofinal n
    exact (hmono hnt).trans htB
  let P : ℕ → Prop := fun d ↦ ∃ n, B - G n = d
  have hP : ∃ d, P d := ⟨B - G 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hP
  refine ⟨N, fun n hn ↦ ?_⟩
  have hGNle : G N ≤ G n := hmono hn
  have hSubLe : B - G n ≤ B - G N := by omega
  have hMin : B - G N ≤ B - G n := by
    rw [hN]
    exact Nat.find_min' hP ⟨n, rfl⟩
  have hSubEq : B - G n = B - G N := Nat.le_antisymm hSubLe hMin
  have hBn := hbound n
  have hBN := hbound N
  omega

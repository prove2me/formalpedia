-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_dvdChain_eventuallyConstant_of_cofinally_bounded
-- name    : ErdosProblems.Erdos243.dvdChain_eventuallyConstant_of_cofinally_bounded
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:27:59.232181+00:00
-- url     : https://prove2.me/theorems/01b4f111-6043-43d9-a3a7-1b42f8d8e90e
-- title:
--   Lean source theorem: dvdChain_eventuallyConstant_of_cofinally_bounded
-- statement:
--   A positive natural-number divisibility chain G(n)∣G(n+1) is eventually constant if every tail contains some value no greater than a fixed bound B.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1603-L1632
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

namespace ErdosProblems.Erdos243
end ErdosProblems.Erdos243

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

open ErdosProblems.Erdos243

theorem ErdosProblems.Erdos243.dvdChain_eventuallyConstant_of_cofinally_bounded
    (G : ℕ → ℕ) (B : ℕ)
    (hpos : ∀ n, 0 < G n)
    (hchain : ∀ n, G n ∣ G (n + 1))
    (hcofinal : ∀ n, ∃ t, n ≤ t ∧ G t ≤ B) :
    ∃ N, ∀ n, N ≤ n → G n = G N := by sorry

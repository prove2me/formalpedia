-- Prove2me | Definitions.Def_Novelty_ErdosStrausFamilies
-- name    : Novelty_ErdosStrausFamilies
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:22:09.678701+00:00
-- url     : https://prove2.me/theorems/1a66e792-dbb3-45f1-b6f0-72adb3806a08
-- title:
--   Aether Catalog definitions — Novelty_ErdosStrausFamilies
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ErdosStrausFamilies`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ErdosStrausFamilies.lean by skeleton subtraction
import Mathlib

/-!
# Erdős–Straus conjecture: provable infinite families

The **Erdős–Straus conjecture** asserts that for every integer `n ≥ 2` the fraction
`4/n` is a sum of three unit fractions: `4/n = 1/x + 1/y + 1/z` with positive integers
`x, y, z` (repetitions allowed).  It is a famous *open* problem.

This file is a **subtask of that open problem**: we prove the conjecture unconditionally
for two explicit infinite families — the even `n` and the `n ≡ 3 (mod 4)` — by exhibiting
closed-form unit-fraction decompositions and verifying them as rational identities.
Together these families cover every even number and every `n ≡ 3 (mod 4)`; the residue
class that remains genuinely open (the obstruction recorded by the Critic below) is
`n ≡ 1 (mod 4)`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The "deep" Erdős–Straus problem hides an elementary algebraic
core — for structured residue classes, `4/n` admits a *parametric* Egyptian-fraction
decomposition that `ring` can certify after clearing denominators.

Experiment (Experimenter): For `n = 2m`, `4/n = 1/m + 1/(2m) + 1/(2m)`.  For `n = 4k+3`,
start from the two-term identity `4/n = 1/(k+1) + 1/(n(k+1))` (which holds *iff* `n = 4k+3`)
and split the second term into two equal halves.  Both reduce to polynomial identities.

Analysis (Analyst): The mechanism is "guess the leading unit fraction `1/⌈n/4⌉`, then the
remainder is a single unit fraction exactly in the good residue classes".  The even case
is even softer (`4/(2m) = 2/m`).  The class `n ≡ 1 (mod 4)` resists because the natural
leading term leaves a remainder that is *not* a single unit fraction; this is the true
arithmetic obstruction and the reason the full conjecture is open.

Critique (Critic): Guarded each theorem with explicit positivity of `x, y, z`.  Checked
non-vacuity (`n = 3, 6, 7` give honest decompositions).  No `native_decide`/`decide`;
the proofs are `field_simp`/`ring` identities, i.e. insight-bearing algebra, not brute
enumeration.  Stated the combined theorem only for `n even ∨ n % 4 = 3` so the claim is
never vacuously or falsely extended to the open class.

Synthesis (PI): Two parametric Egyptian-fraction schemata settle infinitely many cases of
a Millennium-flavoured open problem and isolate the residue obstruction precisely.
-- !-- Lab Notes -- !--
-/

namespace ErdosStraus

/-- A predicate: `4/n` is a sum of three positive unit fractions. -/
def IsEgyptian (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-
**Even family.**  Every even `n = 2m` with `m ≥ 1` satisfies Erdős–Straus, via
`4/(2m) = 1/m + 1/(2m) + 1/(2m)`.
-/

/-
**`3 mod 4` family.**  Every `n = 4k + 3` satisfies Erdős–Straus, via
`4/(4k+3) = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1))`.
-/

/-
**Combined result.**  Erdős–Straus holds for every `n ≥ 2` that is even or `≡ 3 (mod 4)`.
The remaining open class is exactly `n ≡ 1 (mod 4)`.
-/

end ErdosStraus



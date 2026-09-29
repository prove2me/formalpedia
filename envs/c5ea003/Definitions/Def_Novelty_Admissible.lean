-- Prove2me | Definitions.Def_Novelty_Admissible
-- name    : Novelty_Admissible
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T13:59:56.676102+00:00
-- url     : https://prove2.me/theorems/99235489-8ffb-4f30-bb7a-e0353bff4bf5
-- title:
--   Aether Catalog definitions — Novelty_Admissible
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Admissible`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Admissible.lean by skeleton subtraction
import Mathlib
/-
# Admissible prime tuples (Hardy–Littlewood / Maynard–Tao framework)

A finite set `H ⊆ ℤ` is **admissible** if for every prime `p` the residues
`{h mod p : h ∈ H}` do *not* cover all of `ℤ/pℤ`.  Admissibility is the exact
local obstruction in the prime `k`-tuple conjecture: if `H` is *not* admissible
then for some prime `p` every translate `{n + h : h ∈ H}` contains a multiple of
`p`, so it cannot consist entirely of (large) primes.  Conversely the
Hardy–Littlewood conjecture predicts that every admissible tuple is realised by
infinitely many all-prime translates, and the Maynard–Tao theorem proves a
quantitative version of this that yields bounded gaps between primes.

This file develops the *combinatorial core* of the framework, entirely
elementarily:

* `IsAdmissible` — the definition via missing residue classes.
* `exists_missing_residue` — a pigeonhole lemma: any prime `p` larger than `H.card`
  automatically has a missing residue (a `k`-element set cannot cover `p > k`
  classes).
* `isAdmissible_iff_small_primes` — consequently admissibility is a *finite* check:
  it suffices to test primes `p ≤ H.card`.  This is the structural theorem that
  makes admissibility decidable.
* `twinTuple_admissible` — the twin-prime tuple `{0, 2}` is admissible.
* `consecutive_not_admissible` — the tuple `{0, 1}` is *not* admissible (it covers
  both classes mod `2`), explaining why `n` and `n+1` are never both large primes.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): admissibility, a condition quantified over *all* primes,
is in fact a finite condition because large primes cannot be covered by a small set.
Experiment (Experimenter): formalised the pigeonhole reduction and verified the two
witness tuples `{0,2}` (admissible) and `{0,1}` (inadmissible) via `decide` over `ZMod 2`.
Analysis (Analyst): the cutoff is exactly `H.card`; for `p > H.card` the image of `H`
in `ZMod p` has `< p` elements, hence misses a class.  The "all primes" quantifier
collapses to "primes `≤ k`".
Critique (Critic): the result is non-vacuous — `isAdmissible_iff_small_primes` is a
genuine `Iff` whose backward direction needs the pigeonhole lemma, not `decide`.
Synthesis (PI): admissibility is the local input; bounded gaps (see `BoundedGaps.lean`)
is the analytic output; `MaynardTao.lean` bridges them.
-- !-- end Lab Notes -- !--
-/

namespace TwinPrimeGaps

open Finset

/-- A finite set of integers `H` is **admissible** if for every prime `p` there is a
residue class `r mod p` hit by no element of `H`. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-
Pigeonhole: if a prime `p` exceeds the size of `H`, then `H` cannot cover all of
`ℤ/pℤ`, so some residue class is missing.
-/

/-
**Structural theorem.** Admissibility is a finite check: it suffices to verify the
missing-residue condition for primes `p ≤ H.card`.
-/

/-
The twin-prime tuple `{0, 2}` is admissible.
-/

/-
The tuple `{0, 1}` is **not** admissible: modulo `2` it covers both residue classes,
so `n` and `n + 1` are never simultaneously large primes.
-/

end TwinPrimeGaps



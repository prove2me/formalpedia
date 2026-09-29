-- Prove2me | Definitions.Def_Applications_PruningSpectra
-- name    : Applications_PruningSpectra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:29.374659+00:00
-- url     : https://prove2.me/theorems/c3dbeb4c-ac5c-4c1b-870d-974ac050d8b9
-- title:
--   Aether Catalog definitions — Applications_PruningSpectra
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PruningSpectra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PruningSpectra.lean by skeleton subtraction
import Mathlib

/-!
# Arithmetic spectra and component-count saturation

This file isolates two deterministic mechanisms used in limit-law arguments for
component-pruned sparse random structures.

* `EventuallyPeriodic` is the one-dimensional form of semilinearity relevant to
  order spectra.  We prove closure under Boolean operations.
* `CountEquivalent q` records a component multiplicity exactly below `q` and only
  records "at least `q`" above it.  We prove that disjoint union (addition) respects
  this finite-state abstraction.

The final theorem is contrarian: an unrestricted, input-dependent pruning shift
can turn the finite spectrum `{0}` into an arbitrary prescribed tail.  Thus
semilinearity of the unpruned spectrum alone cannot imply a limit law when the
cutoff is allowed to oscillate without regularity assumptions.
-/

namespace ComponentPrunedLimitLaws

/-- A set of natural numbers is eventually periodic if membership is invariant
under a fixed positive translation beyond some threshold. -/
def EventuallyPeriodic (S : Set ℕ) : Prop :=
  ∃ N q : ℕ, 0 < q ∧ ∀ n, N ≤ n → (n ∈ S ↔ n + q ∈ S)






/-
Eventual periodicity depends only on a tail of the set.
-/

/-
Any finite Boolean combination of eventually periodic spectra is eventually
periodic.  This is the arithmetic closure step behind finite-state
Feferman--Vaught reductions.
-/

/-- Multiplicities are indistinguishable at rank `q` when they agree below `q`,
and all values at least `q` are identified. -/
def CountEquivalent (q a b : ℕ) : Prop := a = b ∨ (q ≤ a ∧ q ≤ b)




/-
The saturated component-count abstraction is a congruence for disjoint
union: component multiplicities add.
-/

/-
Coordinatewise saturation is likewise preserved when two component profiles
are combined by disjoint union.
-/

/-- Shifting a spectrum by a varying cutoff.  Natural subtraction models the
residual order after deleting a cutoff-sized initial contribution. -/
def ShiftedSpectrum (S : Set ℕ) (f : ℕ → ℕ) : Set ℕ :=
  {n | n - f n ∈ S}

/-- Given any target set `A`, this cutoff leaves residual order `0` on `A` and
residual order `1` off `A`, away from the unavoidable boundary point `0`. -/
def adversarialCutoff (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  if n ∈ A then n else n - 1

/-
**Disproof of unrestricted pruning invariance.**  Although `{0}` is a finite,
hence eventually periodic, spectrum, an input-dependent cutoff can encode an
arbitrary set `A` on every positive order.  Consequently no semilinearity theorem
can survive arbitrary oscillating pruning thresholds without extra hypotheses.
-/

/-
The base spectrum used in the counterexample is genuinely eventually
periodic.
-/

/-- The sparse set of powers of two. -/
def PowersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

/-
Powers of two are not eventually periodic: every proposed positive period
is eventually shorter than the gap between consecutive powers.
-/

/-
A concrete oscillating cutoff turns the eventually periodic singleton
spectrum into the non-eventually-periodic powers-of-two spectrum on all positive
indices.
-/

/-
**Concrete contrarian conclusion.**  There are an eventually periodic base
spectrum and a cutoff whose shifted spectrum is not eventually periodic.
-/

end ComponentPrunedLimitLaws



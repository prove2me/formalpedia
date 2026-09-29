-- Prove2me | solution 1 for ComponentPrunedLimitLaws.EventuallyPeriodic.inter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:22:21.409127+00:00
-- url     : https://prove2.me/submissions/3524705f-c421-483f-9184-1c0224bb5c74

-- Sol generated from Applications/PruningSpectra.lean
import Mathlib
import Definitions.Def_Applications_PruningSpectra

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

open ComponentPrunedLimitLaws







/-
Eventual periodicity depends only on a tail of the set.
-/

/-
Any finite Boolean combination of eventually periodic spectra is eventually
periodic.  This is the arithmetic closure step behind finite-state
Feferman--Vaught reductions.
-/





/-
The saturated component-count abstraction is a congruence for disjoint
union: component multiplicities add.
-/

/-
Coordinatewise saturation is likewise preserved when two component profiles
are combined by disjoint union.
-/



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


open ComponentPrunedLimitLaws in
theorem solution{S T : Set ℕ}
    (hS : EventuallyPeriodic S) (hT : EventuallyPeriodic T) :
    EventuallyPeriodic (S ∩ T) := by
      obtain ⟨ N₁, q₁, hq₁, hS ⟩ := hS;
      obtain ⟨ N₂, q₂, hq₂, hT ⟩ := hT;
      refine' ⟨ Max.max N₁ N₂, q₁ * q₂, by positivity, fun n hn => _ ⟩;
      -- By induction on $k$, we can show that $n + kq₁ \in S$ if and only if $n \in S$ for any $k \geq 0$.
      have h_ind_S : ∀ k : ℕ, n + k * q₁ ∈ S ↔ n ∈ S := by
        intro k; induction' k with k ih <;> simp_all +decide [ Nat.succ_mul, ← add_assoc ] ;
        grind;
      -- By induction on $k$, we can show that $n + kq₂ \in T$ if and only if $n \in T$ for any $k \geq 0$.
      have h_ind_T : ∀ k : ℕ, n + k * q₂ ∈ T ↔ n ∈ T := by
        intro k; induction' k with k ih <;> simp_all +decide [ Nat.succ_mul, ← add_assoc ] ;
        grind;
      simp +decide [mul_comm q₁ q₂, h_ind_S];
      exact fun _ => by rw [ mul_comm, h_ind_T ] ;

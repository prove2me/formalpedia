-- Prove2me | Theorems.Thm_ComponentPrunedLimitLaws_powersOfTwo_not_eventuallyPeriodic
-- name    : ComponentPrunedLimitLaws.powersOfTwo_not_eventuallyPeriodic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:29:24.381591+00:00
-- url     : https://prove2.me/theorems/b8dc7b45-cabd-49bd-988e-6ba583bc7186
-- title:
--   PowersOfTwo not eventuallyPeriodic
-- statement:
--   Formal statement of `ComponentPrunedLimitLaws.powersOfTwo_not_eventuallyPeriodic` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ComponentPrunedLimitLaws.powersOfTwo_not_eventuallyPeriodic: ¬ EventuallyPeriodic PowersOfTwo := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PosetTheory/PruningSpectra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PosetTheory/PruningSpectra.lean#L158

-- Thm stub generated from Applications/PruningSpectra.lean
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

theorem ComponentPrunedLimitLaws.powersOfTwo_not_eventuallyPeriodic: ¬ EventuallyPeriodic PowersOfTwo := by sorry

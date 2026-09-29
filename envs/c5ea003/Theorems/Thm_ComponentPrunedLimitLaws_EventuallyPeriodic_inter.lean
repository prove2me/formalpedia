-- Prove2me | Theorems.Thm_ComponentPrunedLimitLaws_EventuallyPeriodic_inter
-- name    : ComponentPrunedLimitLaws.EventuallyPeriodic.inter
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:29:22.98578+00:00
-- url     : https://prove2.me/theorems/f794928b-b76a-4e54-85c6-2023530d9193
-- title:
--   Inter
-- statement:
--   Formal statement of `ComponentPrunedLimitLaws.EventuallyPeriodic.inter` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ComponentPrunedLimitLaws.EventuallyPeriodic.inter{S T : Set ℕ}
--       (hS : EventuallyPeriodic S) (hT : EventuallyPeriodic T) :
--       EventuallyPeriodic (S ∩ T) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PosetTheory/PruningSpectra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PosetTheory/PruningSpectra.lean#L41

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

theorem ComponentPrunedLimitLaws.EventuallyPeriodic.inter{S T : Set ℕ}
    (hS : EventuallyPeriodic S) (hT : EventuallyPeriodic T) :
    EventuallyPeriodic (S ∩ T) := by sorry

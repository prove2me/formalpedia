-- Prove2me | Theorems.Thm_Hadwiger_hadwigerProperty_iff_minDegree
-- name    : Hadwiger.hadwigerProperty_iff_minDegree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T14:00:25.813685+00:00
-- url     : https://prove2.me/theorems/ce290d30-f7f0-488d-b68e-bc0afbba5765
-- title:
--   The minimum-degree reduction is an equivalence.
-- statement:
--   **The minimum-degree reduction is an equivalence.**  Hadwiger's conjecture
--   for `k` holds if and only if it holds for non-`k`-colourable graphs of minimum
--   degree at least `k`.
--
--   ```lean
--   theorem Hadwiger.hadwigerProperty_iff_minDegree(k : ℕ) :
--       HadwigerProperty k ↔ HadwigerMinDegreeProperty k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerCriticalEquiv.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerCriticalEquiv.lean#L123

-- Thm stub generated from Probability/HadwigerCriticalEquiv.lean
import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerCriticalEquiv
import Definitions.Def_Probability_HadwigerSmallCases
/-
  # Hadwiger's conjecture is equivalent to its vertex-critical fragment

  This file settles the vertex-critical form of Conjecture 4 of
  `FUTURE_DIRECTIONS.md`: Hadwiger's conjecture for a parameter `k` need only be
  checked on *vertex-critical* graphs, i.e. graphs that are not `k`-colourable
  but become `k`-colourable after the deletion of any single vertex.

      `HadwigerProperty k ↔ HadwigerCriticalProperty k`   (`hadwigerProperty_iff_critical`)

  The `←` direction is the substantial one: a minimal non-`k`-colourable vertex
  subset (`exists_critical_subset`, from `HadwigerCritical.lean`) induces a
  vertex-critical subgraph, and a `K_{k+1}` minor of an induced subgraph is a
  `K_{k+1}` minor of the ambient graph (`isMinor_of_isMinor_induce`).

  The bridge between the ambient-colouring predicate `ColorableOn` and
  colourability of the induced subgraph is `colorableOn_iff_induce`, valid as
  soon as one colour is available; the degenerate parameter `k = 0` is covered by
  the already-proved `hadwiger_zero`.

  -- !-- Lab Notes -- !--
  * No graph isomorphism is needed to see that deleting a vertex from an induced
    subgraph is again an induced subgraph: a colouring of `G.induce ↑(S.erase x)`
    can be *restricted* along the two coercions, which is what
    `colorable_induce_compl_of_colorableOn_erase` does.
  * The equivalence makes "minimal counterexample" arguments available inside the
    formal development: any counterexample to `HadwigerProperty k` yields a
    vertex-critical one.
-/

open Hadwiger

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}





/-! ## The minimum-degree fragment -/

theorem Hadwiger.hadwigerProperty_iff_minDegree(k : ℕ) :
    HadwigerProperty k ↔ HadwigerMinDegreeProperty k := by sorry

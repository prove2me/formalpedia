-- Prove2me | Theorems.Thm_pairPenalty_eq_zero_iff
-- name    : pairPenalty_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:41:19.631071+00:00
-- url     : https://prove2.me/theorems/e05cdc17-b617-4ff4-9b03-c5c431afce65
-- title:
--   PairPenalty eq zero iff
-- statement:
--   Formal statement of `pairPenalty_eq_zero_iff` from the Aether Catalog (Tropical). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem pairPenalty_eq_zero_iff(i j : Voice) (v w : Chord) :
--       pairPenalty i j v w = 0 ↔ PairLegal i j v w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/SATB/TropicalHypergraphCounterpoint.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/SATB/TropicalHypergraphCounterpoint.lean#L167

-- Thm stub generated from Tropical/SATB/TropicalHypergraphCounterpoint.lean
import Mathlib
import Definitions.Def_Tropical_SATB_TropicalHypergraphCounterpoint

/-!
# Tropical Hypergraph Counterpoint for SATB

This module establishes an exact bridge between four-voice (SATB) counterpoint
legality and tropical optimization on weighted hypergraphs.

## Mathematical Content

We model SATB voice leading as a constrained dynamical system on `Fin 4 → ℤ`
and prove three main theorem packages:

### Theorem Package 1: Zero-Locus Characterization
Legal SATB transitions are exactly the zero locus of a nonnegative tropical
penalty functional assembled from six pairwise components (one per unordered
voice pair). This converts Boolean legality into tropical vanishing.

### Theorem Package 2: Shortest-Path Realization
Legal progressions (sequences of chords) are exactly zero-cost paths in the
induced weighted hypergraph. Since all edge weights are nonnegative, legal
paths are globally shortest among all paths with the same endpoints.

### Theorem Package 3: Pairwise Tensor Factorization
The total SATB cost factorizes as a double sum over voice pairs and time steps.
Legality of a full progression is determined entirely by pairwise legality at
each time step, establishing an exact structural decomposition of the 4-voice
problem into coupled 2-voice subproblems.

## Significance

This formalization proves that a high-arity symbolic constraint system (4-voice
counterpoint) admits exact tropical optimization with:
- certifiable legality detection via zero-locus testing,
- shortest-path semantics for legal progressions,
- nontrivial state-space compression via pairwise factorization.
-/

open Finset BigOperators

noncomputable section

/-! ## Core Definitions -/





/-! ## Pairwise Legality Predicates -/









/-! ## Global Legality -/





/-! ## Pairwise Penalty Functions -/






/-! ## Component Penalty Properties -/







/-! ## Pairwise Penalty Zero-Locus -/

theorem pairPenalty_eq_zero_iff(i j : Voice) (v w : Chord) :
    pairPenalty i j v w = 0 ↔ PairLegal i j v w := by sorry

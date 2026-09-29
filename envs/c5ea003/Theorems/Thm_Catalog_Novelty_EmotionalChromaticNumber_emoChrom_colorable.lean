-- Prove2me | Theorems.Thm_Catalog_Novelty_EmotionalChromaticNumber_emoChrom_colorable
-- name    : Catalog.Novelty.EmotionalChromaticNumber.emoChrom_colorable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T14:13:36.249487+00:00
-- url     : https://prove2.me/theorems/4321aaa3-4886-4dda-ae9c-b63c62b2ab15
-- title:
--   The value is realizable: `G` genuinely admits a proper coloring with `emoChrom G` emotions.
-- statement:
--   The value is realizable: `G` genuinely admits a proper coloring with `emoChrom G` emotions.
--
--   ```lean
--   theorem Catalog.Novelty.EmotionalChromaticNumber.emoChrom_colorable(G : SimpleGraph V) : G.Colorable (emoChrom G) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/EmotionalChromaticNumber.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/EmotionalChromaticNumber.lean#L105

-- Thm stub generated from Geometry/EmotionalChromaticNumber.lean
import Mathlib
import Definitions.Def_Geometry_EmotionalChromaticNumber
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Emotional Chromatic Number of a Social Network

Model a social network as a finite simple graph `G`: vertices are people and edges are
friendships.  A proper coloring with `k` colors is an assignment of one of `k` *emotions* to each
person so that no two friends share the same emotion.  The chromatic counting function
`chromVal G k` (developed in `Catalog/Combinatorics/ChromaticPolynomial.lean`) counts such
assignments, and `G.Colorable k` records whether at least one exists.

We isolate the *emotional* regime, where a genuine assignment must use at least three emotion
categories (two-emotion assignments are dismissed as trivial "bipartite" splits).  The
**emotional chromatic number**

  `emoChrom G  =  min { k : 3 ≤ k and G is k-colorable }`

is the smallest number of emotions `≥ 3` that suffices for a consistent assignment.

## Main results

* `emoChrom_ge_three`      : `3 ≤ emoChrom G`               (the emotional floor).
* `emoChrom_colorable`     : `G.Colorable (emoChrom G)`     (the value is attained).
* `emoChrom_le`            : minimality among admissible color counts.
* `emoChrom_eq_three_iff`  : `emoChrom G = 3 ↔ G.Colorable 3`.
* `emoChrom_complete`      : `emoChrom (K_n) = max n 3`     (a clique of `n` mutual friends).
* `emoChrom_complete_ge_three` : for `n ≥ 3`, `emoChrom (K_n) = n`.
* `emoChrom_cycle`         : `emoChrom (C_n) = 3` for every `n ≥ 3` (friendship circles).
* `emotionally_consistent` : if `G` is `6`-colorable then `3 ≤ emoChrom G ≤ 6`
                             (the six basic emotions suffice, and three are always needed).
* `emoChrom_bipartite_floor` : the complete bipartite pair `K_2` is `2`-colorable yet has
                             emotional chromatic number `3` — the emotional floor bites.
* `chromVal_two_of_edge_pos` / `bipartite_root_claim_false` : a graph that splits into two
                             groups is *not* a root of the chromatic polynomial at `k = 2`;
                             the true obstruction lives at `k = 1`.

-- !-- Lab Notes -- !--
HYPOTHESIS.  Restricting proper colorings to the "emotional" range `k ≥ 3` should collapse the
chromatic number to a small window.  Concretely: cliques should force `emoChrom = n`, cycles should
always land on `3` (even cycles, which are bipartite, are pushed up from `2` by the emotional floor),
and any network colorable with the six basic emotions should satisfy `3 ≤ emoChrom ≤ 6`.

EXPERIMENTAL PLAN.
  (1) Define `emoChrom` as the infimum of the admissible set `{k | 3 ≤ k ∧ G.Colorable k}` and show
      the set is nonempty (a finite graph is colorable with `card V` colors).
  (2) Read off the defining properties from `Nat.sInf_mem` / `Nat.sInf_le`.
  (3) Feed the falling-factorial evaluation of the complete graph (`complete_colorable_iff`) into the
      infimum to get `emoChrom (K_n) = max n 3`.
  (4) Use Mathlib's `chromaticNumber_cycleGraph_of_even/odd` to get `C_n.Colorable 3`, then pin the
      cycle value to the floor `3`.
  (5) Refute the folklore "bipartite root at k = 2" claim by computing `chromVal (K_2) 2 = 2`.

INSIGHT.  Colorability is monotone (`Colorable.mono`), so the admissible set `{k | 3 ≤ k ∧ Colorable k}`
is an up-set intersected with `[3, ∞)`; its infimum is therefore `max (χ G) 3` in spirit.  This is
why every bipartite network (chromatic number `2`) has emotional chromatic number exactly `3`: the
floor, not the graph, decides.  The complete graph is the unique obstruction that pushes the value
strictly above `3`, and only when the clique already needs `≥ 3` colors.

ANALYSIS / CRITIQUE.  The description's assertion that "the chromatic polynomial has a root at
`k = 2` for any bipartite graph" is FALSE: a bipartite graph with an edge has *positive* chromatic
polynomial at `2` (e.g. `chromVal (K_2) 2 = 2`).  The genuine root common to every graph with an edge
sits at `k = 1`.  We record the corrected statements `chromVal_two_of_edge_pos` and
`bipartite_root_claim_false`, and encode the intended phenomenon — that two emotions are declared
insufficient — as the *emotional floor* `emoChrom ≥ 3` rather than as a spurious polynomial root.
-- !-- End Lab Notes -- !--
-/

open Catalog.Novelty.EmotionalChromaticNumber

open SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definition and basic API -/





omit [DecidableEq V] in

theorem Catalog.Novelty.EmotionalChromaticNumber.emoChrom_colorable(G : SimpleGraph V) : G.Colorable (emoChrom G) := by sorry

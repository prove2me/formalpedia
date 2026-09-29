-- Prove2me | Theorems.Thm_octahedron_not_cliqueHelly
-- name    : octahedron_not_cliqueHelly
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:02:36.63545+00:00
-- url     : https://prove2.me/theorems/503a083a-73c6-4184-8ad5-42efb283ac7b
-- title:
--   The octahedron graph `K_{2,2,2}` is not clique-Helly.
-- statement:
--   The octahedron graph `K_{2,2,2}` is **not** clique-Helly.
--
--   The family `{{0,2,4}, {0,3,5}, {1,2,5}}` consists of maximal cliques that
--   pairwise intersect (`pairwise_intersect`) yet have empty total intersection
--   (`total_intersection_empty`), contradicting the Helly property.
--
--   ```lean
--   theorem octahedron_not_cliqueHelly: ¬ CliqueHelly octahedron := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/RamseyTheory/OctahedronNotCliqueHelly.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/RamseyTheory/OctahedronNotCliqueHelly.lean#L131

-- Thm stub generated from MachineLearning/RamseyTheory/OctahedronNotCliqueHelly.lean
import Mathlib
import Definitions.Def_MachineLearning_RamseyTheory_OctahedronNotCliqueHelly

/-!
# The octahedron graph `K_{2,2,2}` is not clique-Helly

This file gives a self-contained, minimal formalization of the fact that the
octahedron graph (the complete tripartite graph `K_{2,2,2}`) is **not**
clique-Helly.

The vertex set is `Fin 6`, split into three parts of size two according to
`i / 2`:

* part `0` = `{0, 1}`,
* part `1` = `{2, 3}`,
* part `2` = `{4, 5}`.

Two vertices are adjacent iff they are distinct and lie in different parts.

A graph is *clique-Helly* if every family of maximal cliques that pairwise
intersect has a common vertex.  We exhibit three maximal cliques
`{0,2,4}`, `{0,3,5}`, `{1,2,5}` that pairwise intersect but have empty total
intersection, witnessing the failure of the Helly property.
-/

open SimpleGraph

theorem octahedron_not_cliqueHelly: ¬ CliqueHelly octahedron := by sorry

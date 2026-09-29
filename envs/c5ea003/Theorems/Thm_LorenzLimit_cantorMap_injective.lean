-- Prove2me | Theorems.Thm_LorenzLimit_cantorMap_injective
-- name    : LorenzLimit.cantorMap_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:07:02.097035+00:00
-- url     : https://prove2.me/theorems/795c3709-d5e7-4691-b3c0-e840b32c8792
-- title:
--   CantorMap injective
-- statement:
--   Formal statement of `LorenzLimit.cantorMap_injective` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LorenzLimit.cantorMap_injective(v₀ : V) : Function.Injective (cantorMap h v₀) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/StrangeAttractorTopology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/StrangeAttractorTopology.lean#L107

-- Thm stub generated from Novelty/StrangeAttractorTopology.lean
import Mathlib
import Definitions.Def_Novelty_StrangeAttractorInverseLimit
import Definitions.Def_Novelty_StrangeAttractorTopology

/-!
# Strange attractors as algebraic objects, IV: the topology of the inverse limit

The inverse limit of the finite path diagram of a finite directed graph is not merely a set:
it carries the inverse-limit topology, inherited from the product of discrete finite sets.
Here we prove that it has exactly the topological features expected of a strange attractor's
transversal structure:

* `isClosed_pathSet`, `isCompact_pathSet` : the orbit space is a compact (closed) subset of
  the Cantor-type product space, so the inverse limit of finite graphs is compact;
* `continuous_shift` : the shift is continuous, so `(PathSpace E, shift)` is a topological
  dynamical system;
* `cantorMap_isClosedEmbedding` : if every vertex branches (out-degree `≥ 2`) the attractor
  contains a topologically embedded Cantor set;
* `uncountable_pathSpace` : consequently the attractor is uncountable, while every finite
  approximant is finite — the inverse limit is a genuinely infinite object;
* `perfect_pathSet` : a branching attractor has no isolated orbits, so it is a perfect,
  compact, totally disconnected, Hausdorff space.

Together with the compactness, total disconnectedness and Hausdorffness instances this says
that a branching symbolic attractor is a Cantor-type space.
-/

open LorenzLimit

variable {V : Type*} [Fintype V] [TopologicalSpace V] [DiscreteTopology V] {E : V → V → Bool}

/-! ## Compactness and total disconnectedness -/







/-! ## The shift is continuous -/


/-! ## An embedded Cantor set -/


variable (h : Branching E)








omit [Fintype V] [TopologicalSpace V] [DiscreteTopology V] in

theorem LorenzLimit.cantorMap_injective(v₀ : V) : Function.Injective (cantorMap h v₀) := by sorry

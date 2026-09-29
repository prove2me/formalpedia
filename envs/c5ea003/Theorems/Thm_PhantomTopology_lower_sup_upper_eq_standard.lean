-- Prove2me | Theorems.Thm_PhantomTopology_lower_sup_upper_eq_standard
-- name    : PhantomTopology.lower_sup_upper_eq_standard
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:40:49.103169+00:00
-- url     : https://prove2.me/theorems/09387ea3-b1d8-47b0-a252-d1a0c57b6484
-- title:
--   A set simultaneously lower- and upper-limit open is Euclidean open, and
-- statement:
--   A set simultaneously lower- and upper-limit open is Euclidean open, and
--   conversely.  Thus the standard topology is the observers' agreement topology.
--
--   ```lean
--   theorem PhantomTopology.lower_sup_upper_eq_standard:
--       lowerTop ⊔ upperTop = (inferInstance : TopologicalSpace ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/PhantomTopologies.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/PhantomTopologies.lean#L111

-- Thm stub generated from Logic/PosetTheory/PhantomTopologies.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_PhantomTopologies
/-
# Phantom Topologies

A phantom topology is an observer-indexed family of topologies.  This file makes
"agreement" precise as the supremum in Mathlib's (reverse-inclusion) lattice of
topologies and develops a chain of results from the general definition to two
substantive examples.

The literal proposed phantom number is degenerate: every topology has a
one-observer representation, obtained by letting that observer see the real
topology itself.  A nontrivial variant requires every observer to be strictly
finer than consensus.  For that variant, the standard topology on `ℝ` has a
genuine two-observer representation by the lower- and upper-limit topologies.
The proposed lower bound for nonmetrizable spaces is false: the indiscrete
space on `Bool` is nonmetrizable yet is the consensus of two strictly finer
Sierpiński topologies.
-/

open Set TopologicalSpace

open PhantomTopology

variable {X ι : Type*}










/-! ## The real line: two half-open observers -/

theorem PhantomTopology.lower_sup_upper_eq_standard:
    lowerTop ⊔ upperTop = (inferInstance : TopologicalSpace ℝ) := by sorry

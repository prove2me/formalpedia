-- Prove2me | Theorems.Thm_PhantomTopology_sierp_sup_eq_indiscrete
-- name    : PhantomTopology.sierp_sup_eq_indiscrete
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:40:42.086105+00:00
-- url     : https://prove2.me/theorems/e2431166-c320-4baf-bc7d-5f4a13828769
-- title:
--   Agreement of the opposite Sierpiński observers is the indiscrete topology.
-- statement:
--   Agreement of the opposite Sierpiński observers is the indiscrete topology.
--
--   ```lean
--   theorem PhantomTopology.sierp_sup_eq_indiscrete:
--       sierpTrue ⊔ sierpFalse = (⊤ : TopologicalSpace Bool) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/PhantomTopologies.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/PhantomTopologies.lean#L241

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















/-! ## A nonmetrizable two-observer counterexample -/

theorem PhantomTopology.sierp_sup_eq_indiscrete:
    sierpTrue ⊔ sierpFalse = (⊤ : TopologicalSpace Bool) := by sorry

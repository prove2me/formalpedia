-- Prove2me | Theorems.Thm_clique_pair_iff
-- name    : clique_pair_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:06:20.517545+00:00
-- url     : https://prove2.me/theorems/2375cdf2-5eb1-4701-ab31-3601e3353e13
-- title:
--   Theorem B.
-- statement:
--   **Theorem B.** For distinct vertices, `{a, b}` is a face of the clique
--   complex iff `a` and `b` are adjacent.
--
--   ```lean
--   theorem clique_pair_iff(G : SimpleGraph α) (a b : α) (h : a ≠ b) :
--       ({a, b} : Finset α) ∈ (cliqueComplex G).faces ↔ G.Adj a b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/FlagComplex.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/FlagComplex.lean#L97

-- Thm stub generated from Geometry/FlagComplex.lean
import Mathlib
import Definitions.Def_Geometry_FlagComplex
/-
  Flag complexes and clique complexes of simple graphs
  ====================================================

  This file formalizes the equivalence between flag complexes and clique
  complexes of simple graphs.

  An abstract simplicial complex `K` is a *flag complex* iff a finite set of
  vertices is a face of `K` exactly when all of its distinct pairs are edges of
  the 1-skeleton of `K`.  The clique complex of a graph `G` is the simplicial
  complex whose faces are the cliques of `G`.  The main results show that the
  clique complex of any graph is flag, and that an abstract simplicial complex
  is flag if and only if it equals the clique complex of its own 1-skeleton.
-/

open Finset

variable {α : Type*} [DecidableEq α]

theorem clique_pair_iff(G : SimpleGraph α) (a b : α) (h : a ≠ b) :
    ({a, b} : Finset α) ∈ (cliqueComplex G).faces ↔ G.Adj a b := by sorry

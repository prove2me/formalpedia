-- Prove2me | Theorems.Thm_IsFlag_eq_cliqueComplex
-- name    : IsFlag.eq_cliqueComplex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:30:16.707359+00:00
-- url     : https://prove2.me/theorems/5ddfae1c-85a0-4e91-a00a-3ddcd8132cba
-- title:
--   Theorem D.
-- statement:
--   **Theorem D.** A flag complex equals the clique complex of its 1-skeleton.
--
--   ```lean
--   theorem IsFlag.eq_cliqueComplex(K : ASC α) (hK : IsFlag K) :
--       K.faces = (cliqueComplex (oneSkel K)).faces := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/FlagComplex.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/FlagComplex.lean#L120

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

theorem IsFlag.eq_cliqueComplex(K : ASC α) (hK : IsFlag K) :
    K.faces = (cliqueComplex (oneSkel K)).faces := by sorry

-- Prove2me | Theorems.Thm_ErdosFaberLovasz_erase_disjoint_of_common_vertex
-- name    : ErdosFaberLovasz.erase_disjoint_of_common_vertex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T14:24:28.009145+00:00
-- url     : https://prove2.me/theorems/2a3942e4-828e-44dd-aed6-1e26e427ad28
-- title:
--   Two distinct edges through the same vertex have disjoint sets of remaining vertices.
-- statement:
--   Two distinct edges through the same vertex have disjoint sets of remaining vertices.
--   This is the local disjointness principle behind the standard EFL degree estimates.
--
--   ```lean
--   theorem ErdosFaberLovasz.erase_disjoint_of_common_vertex{H : Hypergraph V} (hlin : IsLinear H)
--       {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hne : e ≠ f)
--       {x : V} (hxe : x ∈ e) (hxf : x ∈ f) :
--       Disjoint (e.erase x) (f.erase x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/ErdosFaberLovasz.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/ErdosFaberLovasz.lean#L68

-- Thm stub generated from Combinatorics/ErdosFaberLovasz.lean
import Mathlib
import Definitions.Def_Combinatorics_ErdosFaberLovasz

-- open removed: section is not a namespace

open ErdosFaberLovasz

variable {V : Type*} [DecidableEq V]

theorem ErdosFaberLovasz.erase_disjoint_of_common_vertex{H : Hypergraph V} (hlin : IsLinear H)
    {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hne : e ≠ f)
    {x : V} (hxe : x ∈ e) (hxf : x ∈ f) :
    Disjoint (e.erase x) (f.erase x) := by sorry

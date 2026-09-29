-- Prove2me | Definitions.Def_Speculative_SciFi_MindUploading
-- name    : Speculative_SciFi_MindUploading
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:49.67942+00:00
-- url     : https://prove2.me/theorems/37a18108-3513-4f47-9bf7-bf6ddd30e588
-- title:
--   Aether Catalog definitions — Speculative_SciFi_MindUploading
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.SciFi.MindUploading`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/SciFi/MindUploading.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.SciFi.MindUploading

Čech Obstruction to Mind Uploading.

Mathematical Concept: Sheaf cohomology H¹ as an obstruction to global consistency.
A 'mind' is modeled as a sheaf F of local mental states over a topological space X.
-/

universe u

/-- A presheaf on a topological space X -/
structure Presheaf' (X : Type u) [TopologicalSpace X] where
  obj : TopologicalSpace.Opens X → Type u
  map {U V : TopologicalSpace.Opens X} (h : U ≤ V) : obj V → obj U

/-- A sheaf: presheaf with gluing -/
structure Sheaf' (X : Type u) [TopologicalSpace X] extends Presheaf'.{u} X where
  gluing : ∀ {ι : Type u} [DecidableEq ι] (U : ι → TopologicalSpace.Opens X)
    (s : ∀ i, obj (U i)),
    (∀ i j, map inf_le_left (s i) = map inf_le_right (s j)) →
    ∃! s_global : obj (⨆ i, U i), ∀ i, map (le_iSup U i) s_global = s i



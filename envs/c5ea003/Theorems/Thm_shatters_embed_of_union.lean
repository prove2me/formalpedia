-- Prove2me | Theorems.Thm_shatters_embed_of_union
-- name    : shatters_embed_of_union
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:54.906032+00:00
-- url     : https://prove2.me/theorems/5ce14e25-55fd-4e70-a0cf-d24dd3ba7d5d
-- title:
--   Shatters embed of union
-- statement:
--   Formal statement of `shatters_embed_of_union` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem shatters_embed_of_union{n : ℕ} (F : Finset (Finset (Fin (n + 1))))
--       {A : Finset (Fin n)}
--       (h : Shatters ((F.filter (Fin.last n ∉ ·)).image proj ∪
--                       (F.filter (Fin.last n ∈ ·)).image proj) A) :
--       Shatters F (embed A) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SauerShelah.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SauerShelah.lean#L110

-- Thm stub generated from Algebra/SauerShelah.lean
import Mathlib
import Definitions.Def_Algebra_SauerShelah

open Fin

/-! # CatalogBuild.Algebra.SauerShelah

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17
-/











-- ================================================================
--  Basic proj / embed API
-- ================================================================

theorem shatters_embed_of_union{n : ℕ} (F : Finset (Finset (Fin (n + 1))))
    {A : Finset (Fin n)}
    (h : Shatters ((F.filter (Fin.last n ∉ ·)).image proj ∪
                    (F.filter (Fin.last n ∈ ·)).image proj) A) :
    Shatters F (embed A) := by sorry

-- Prove2me | Theorems.Thm_shatters_embed_union_last_of_inter
-- name    : shatters_embed_union_last_of_inter
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:03:12.243118+00:00
-- url     : https://prove2.me/theorems/a060cefe-0b4b-4a9a-b73c-379dab5ddb50
-- title:
--   Shatters embed union last of inter
-- statement:
--   Formal statement of `shatters_embed_union_last_of_inter` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem shatters_embed_union_last_of_inter{n : ℕ} (F : Finset (Finset (Fin (n + 1))))
--       {A : Finset (Fin n)}
--       (h : Shatters ((F.filter (Fin.last n ∉ ·)).image proj ∩
--                       (F.filter (Fin.last n ∈ ·)).image proj) A) :
--       Shatters F (embed A ∪ {Fin.last n}) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SauerShelah.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SauerShelah.lean#L132

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

theorem shatters_embed_union_last_of_inter{n : ℕ} (F : Finset (Finset (Fin (n + 1))))
    {A : Finset (Fin n)}
    (h : Shatters ((F.filter (Fin.last n ∉ ·)).image proj ∩
                    (F.filter (Fin.last n ∈ ·)).image proj) A) :
    Shatters F (embed A ∪ {Fin.last n}) := by sorry

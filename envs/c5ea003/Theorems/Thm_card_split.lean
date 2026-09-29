-- Prove2me | Theorems.Thm_card_split
-- name    : card_split
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:30.074178+00:00
-- url     : https://prove2.me/theorems/458eade9-7580-4e3f-af8f-a829cdae5b27
-- title:
--   Card split
-- statement:
--   Formal statement of `card_split` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem card_split{n : ℕ} (F : Finset (Finset (Fin (n + 1)))) :
--       F.card = ((F.filter (Fin.last n ∉ ·)).image proj ∪
--                 (F.filter (Fin.last n ∈ ·)).image proj).card +
--                ((F.filter (Fin.last n ∉ ·)).image proj ∩
--                 (F.filter (Fin.last n ∈ ·)).image proj).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SauerShelah.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SauerShelah.lean#L170

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

theorem card_split{n : ℕ} (F : Finset (Finset (Fin (n + 1)))) :
    F.card = ((F.filter (Fin.last n ∉ ·)).image proj ∪
              (F.filter (Fin.last n ∈ ·)).image proj).card +
             ((F.filter (Fin.last n ∉ ·)).image proj ∩
              (F.filter (Fin.last n ∈ ·)).image proj).card := by sorry

-- Prove2me | Theorems.Thm_iterated_evaders_all_distinct
-- name    : iterated_evaders_all_distinct
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:23:03.461824+00:00
-- url     : https://prove2.me/theorems/4acd79b6-c4b6-4ce0-900c-638823f9723f
-- title:
--   Iterated evaders all distinct
-- statement:
--   Formal statement of `iterated_evaders_all_distinct` from the Aether Catalog (EML). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem iterated_evaders_all_distinct(enum : ℕ → (ℕ → ℕ)) :
--       ∀ i j, i ≠ j → iterated_evader i enum ≠ iterated_evader j enum := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `EML/GameTheory/RepulsorTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/EML/GameTheory/RepulsorTheory.lean#L46

-- Thm stub generated from EML/GameTheory/RepulsorTheory.lean
import Mathlib
import Definitions.Def_EML_GameTheory_RepulsorTheory

/-! # CatalogBuild.Physics.Classical.RepulsorTheory

Auto-generated from theorem catalog database.
Domain: Physics/Classical
Declarations: 33
-/

noncomputable section

theorem iterated_evaders_all_distinct(enum : ℕ → (ℕ → ℕ)) :
    ∀ i j, i ≠ j → iterated_evader i enum ≠ iterated_evader j enum := by sorry

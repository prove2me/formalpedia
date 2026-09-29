-- Prove2me | Theorems.Thm_SheafDatabaseGluing_compatible_has_unique_glue
-- name    : SheafDatabaseGluing.compatible_has_unique_glue
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:58:51.139975+00:00
-- url     : https://prove2.me/theorems/40b0b43e-b4cc-423a-9eb2-aa020ff7d78e
-- title:
--   Database sheaf condition.
-- statement:
--   **Database sheaf condition.** Compatible records have a unique glued
--   record on the union.  Thus consistent imputation is exactly existence and
--   uniqueness of a global section in this deterministic model.
--
--   ```lean
--   theorem SheafDatabaseGluing.compatible_has_unique_glue{U V : Set ι}
--       (s : LocalSection Value U) (t : LocalSection Value V)
--       (hcompat : Compatible Value s t) :
--       ∃! u : LocalSection Value (U ∪ V),
--         (∀ i (hiU : i ∈ U), u i (Set.mem_union_left V hiU) = s i hiU) ∧
--         (∀ i (hiV : i ∈ V), u i (Set.mem_union_right U hiV) = t i hiV) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SheafDatabaseGluing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SheafDatabaseGluing.lean#L70

-- Thm stub generated from Algebra/SheafDatabaseGluing.lean
import Mathlib
import Definitions.Def_Algebra_SheafDatabaseGluing

/-!
# Sheaf-Theoretic Database Gluing

A database view on a set `U` of columns is represented by a dependent function
assigning a value to every column in `U`.  Two views are compatible when their
values agree on `U ∩ V`.  This file proves, in a cumulative chain, the concrete
sheaf gluing theorem for such database views:

1. the canonical glued view restricts to the first view;
2. compatibility makes it restrict to the second view as well;
3. therefore a common extension exists;
4. that common extension is unique.

This is the sheaf condition for the sheaf of dependent records on a discrete
set of columns.  It formalizes the deterministic consistency claim without
assuming a probabilistic missing-data model.
-/

open Classical

open SheafDatabaseGluing

variable {ι : Type*} (Value : ι → Type*)

theorem SheafDatabaseGluing.compatible_has_unique_glue{U V : Set ι}
    (s : LocalSection Value U) (t : LocalSection Value V)
    (hcompat : Compatible Value s t) :
    ∃! u : LocalSection Value (U ∪ V),
      (∀ i (hiU : i ∈ U), u i (Set.mem_union_left V hiU) = s i hiU) ∧
      (∀ i (hiV : i ∈ V), u i (Set.mem_union_right U hiV) = t i hiV) := by sorry

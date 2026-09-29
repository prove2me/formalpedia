-- Prove2me | Theorems.Thm_RootedPathIrregularity_FinGraph_exists_distinct_equal_degree
-- name    : RootedPathIrregularity.FinGraph.exists_distinct_equal_degree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:43:40.462513+00:00
-- url     : https://prove2.me/theorems/da9b8253-4e00-46d8-b950-39c935b1138d
-- title:
--   Exists distinct equal degree
-- statement:
--   Formal statement of `RootedPathIrregularity.FinGraph.exists_distinct_equal_degree` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RootedPathIrregularity.FinGraph.exists_distinct_equal_degree(G : FinGraph V) (hcard : 2 ≤ Fintype.card V) :
--       ∃ v w : V, v ≠ w ∧ G.degree v = G.degree w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/RootedPathIrregularity/Contrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/RootedPathIrregularity/Contrarian.lean#L75

-- Thm stub generated from Logic/RootedPathIrregularity/Contrarian.lean
import Mathlib
import Definitions.Def_Logic_RootedPathIrregularity_Contrarian

/-!
# Contrarian results on rooted three-vertex paths

This file isolates the local counting mechanism behind the exceptional case `P₃`.
It also gives a certified six-vertex counterexample to the tempting conjecture that
ordinary `P₃`-irregularity forces end-rooted `P₃`-irregularity.
-/

open RootedPathIrregularity


open FinGraph

variable {V : Type*} [Fintype V] [DecidableEq V]











/-
Every finite simple graph with at least two vertices has two vertices of equal degree.
-/

theorem RootedPathIrregularity.FinGraph.exists_distinct_equal_degree(G : FinGraph V) (hcard : 2 ≤ Fintype.card V) :
    ∃ v w : V, v ≠ w ∧ G.degree v = G.degree w := by sorry

-- Prove2me | Theorems.Thm_MaximumCliqueReductions_clique_extension_bound
-- name    : MaximumCliqueReductions.clique_extension_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:33.515361+00:00
-- url     : https://prove2.me/theorems/bcafdfa8-7ac7-42cb-928a-63a2032070ff
-- title:
--   The portion of a clique outside a contained pattern is itself a clique in the
-- statement:
--   The portion of a clique outside a contained pattern is itself a clique in the
--   pattern's common neighborhood. Consequently its size is bounded by any clique
--   upper-bound oracle evaluated on that common neighborhood.
--
--   ```lean
--   theorem MaximumCliqueReductions.clique_extension_bound{ub : Set V → ℕ} (hub : IsCliqueUpperBound G ub)
--       {S C D : Set V} (hCfin : C.Finite) (hC : IsClique G C)
--       (hD : D ⊆ C) (hCS : C ⊆ S) :
--       C.ncard ≤ D.ncard + ub (S ∩ commonNeighbors G D) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/RamseyTheory/MaximumCliqueReductions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/RamseyTheory/MaximumCliqueReductions.lean#L36

-- Thm stub generated from Applications/RamseyTheory/MaximumCliqueReductions.lean
import Mathlib
import Definitions.Def_Applications_RamseyTheory_MaximumCliqueReductions

/-!
# Upper-bound-driven reductions for maximum clique

This file isolates the mathematical core of upper-bound-enhanced core and truss
reductions. An upper-bound oracle is treated extensionally: on every vertex set
it bounds the cardinality of every finite clique contained there. The results
show that a clique can contain a proposed pattern only when the oracle value on
its common neighborhood is large enough, and that repeated certified vertex
peeling preserves every clique above the target size.
-/

open Set

open MaximumCliqueReductions

variable {V : Type*} (G : SimpleGraph V)

theorem MaximumCliqueReductions.clique_extension_bound{ub : Set V → ℕ} (hub : IsCliqueUpperBound G ub)
    {S C D : Set V} (hCfin : C.Finite) (hC : IsClique G C)
    (hD : D ⊆ C) (hCS : C ⊆ S) :
    C.ncard ≤ D.ncard + ub (S ∩ commonNeighbors G D) := by sorry

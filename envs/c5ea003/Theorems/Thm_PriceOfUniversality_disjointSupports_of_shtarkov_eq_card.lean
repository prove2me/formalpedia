-- Prove2me | Theorems.Thm_PriceOfUniversality_disjointSupports_of_shtarkov_eq_card
-- name    : PriceOfUniversality.disjointSupports_of_shtarkov_eq_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:23:47.331802+00:00
-- url     : https://prove2.me/theorems/fa99d5ab-9f53-497c-bb8f-5b3221381405
-- title:
--   Rigidity, hard direction: only perfectly distinguishable classes pay the
-- statement:
--   **Rigidity, hard direction**: only perfectly distinguishable classes pay the
--   maximal price `log₂ m`.
--
--   ```lean
--   theorem PriceOfUniversality.disjointSupports_of_shtarkov_eq_card{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
--       (h : shtarkov p = Fintype.card Θ) : DisjointSupports p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyRigidity.lean#L75

-- Thm stub generated from Novelty/UniversalRedundancyRigidity.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
/-
# The price of universality, IX: rigidity of the maximal price

`shtarkov_disjointSupports` showed that `m` perfectly distinguishable sources
cost exactly `log₂ m` bits of universality — the cost of naming the source.
Here we prove the **converse**, and hence a rigidity theorem:

  `S(P) = m`  ⟺  the `m` sources have pairwise disjoint supports,

and, in strict form, **every genuinely overlapping class is strictly cheaper**
than naming its members:

  `¬ DisjointSupports P  →  S(P) < m`  and  `log₂ S(P) < log₂ m`.

So the naive "one code per model, plus a label" scheme is optimal *only* in the
degenerate case where the models never produce the same data; as soon as two
sources share a possible message the universal code strictly beats the labelling
scheme.  This is the precise sense in which the price of universality is a
measure of *statistical distinguishability*, not of class cardinality.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]




omit [Nonempty A] in

theorem PriceOfUniversality.disjointSupports_of_shtarkov_eq_card{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (h : shtarkov p = Fintype.card Θ) : DisjointSupports p := by sorry

-- Prove2me | Theorems.Thm_PriceOfUniversality_shtarkov_le_card
-- name    : PriceOfUniversality.shtarkov_le_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:26:30.558164+00:00
-- url     : https://prove2.me/theorems/e609b954-7605-4f12-94a8-bac642879791
-- title:
--   The counting bound: the Shtarkov sum of a class of `m` sources is at most
-- statement:
--   **The counting bound**: the Shtarkov sum of a class of `m` sources is at most
--   `m`, so the price of universality never exceeds the cost of naming the source.
--
--   ```lean
--   theorem PriceOfUniversality.shtarkov_le_card{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) :
--       shtarkov p ≤ Fintype.card Θ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyRigidity.lean#L39

-- Thm stub generated from Novelty/UniversalRedundancyRigidity.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
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

theorem PriceOfUniversality.shtarkov_le_card{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) :
    shtarkov p ≤ Fintype.card Θ := by sorry

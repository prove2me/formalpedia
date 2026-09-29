-- Prove2me | solution 1 for PriceOfUniversality.shtarkov_eq_card_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:22:33.101086+00:00
-- url     : https://prove2.me/submissions/0c7d5426-bc8e-4706-9ee9-8afcb9dac75c

-- Sol generated from Novelty/UniversalRedundancyRigidity.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_disjointSupports_of_shtarkov_eq_card
import Theorems.Thm_PriceOfUniversality_shtarkov_disjointSupports
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









open PriceOfUniversality in
omit [Nonempty A] in
theorem solution{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) :
    shtarkov p = Fintype.card Θ ↔ DisjointSupports p :=
  ⟨disjointSupports_of_shtarkov_eq_card hp, shtarkov_disjointSupports hp⟩

-- Prove2me | Theorems.Thm_PriceOfUniversality_price_of_universality_sandwich
-- name    : PriceOfUniversality.price_of_universality_sandwich
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:25:28.060111+00:00
-- url     : https://prove2.me/theorems/c12fdb36-fa0f-4ffe-b3a8-a247871e67dd
-- title:
--   The price of universality, exactly.
-- statement:
--   **The price of universality, exactly.** For a class of `m` perfectly
--   distinguishable sources (every message covered), the minimax redundancy is
--   `log₂ m` up to one bit:
--
--   no code can serve the whole class at a cost below `log₂ m` bits on every
--     member, and
--   one explicit code (the Shannon code of the uniform mixture) serves the whole
--     class at a cost of at most `log₂ m + 1` bits.
--
--   Thus universality moves exactly `log₂ m` bits from the shared decompressor into
--   the message: a decompressor specialised to one member of the class saves
--   `log₂ m` bits and no more.
--
--   ```lean
--   theorem PriceOfUniversality.price_of_universality_sandwich[Nonempty Θ] {p : Θ → A → ℝ}
--       (hp : ∀ θ, IsPMF (p θ)) (hdisj : DisjointSupports p)
--       (hcov : ∀ a : A, 0 < mixture (fun _ => (Fintype.card Θ : ℝ)⁻¹) p a) :
--       (∀ L : A → ℕ, IsCode L → ∃ θ, logb 2 (Fintype.card Θ) ≤ redundancy (p θ) L) ∧
--       (∃ L : A → ℕ, IsCode L ∧ ∀ θ, redundancy (p θ) L ≤ logb 2 (Fintype.card Θ) + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyMinimax.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyMinimax.lean#L287

-- Thm stub generated from Novelty/UniversalRedundancyMinimax.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
/-
# The price of universality, II: minimax redundancy and mutual information

A *universal* code must serve every source in a class `{p θ}` with a single
length function `L`, whereas a *specialised* code may be tuned to one source.
The number of extra bits this costs is the **price of universality**.

Main results of this file, for a finite class `Θ` of sources on a finite
alphabet `A`:

* `kl_compensation` — the exact decomposition
  `∑ θ, π θ * D(p θ ‖ q) = I(π) + D(mixture ‖ q)`, valid for every coding
  distribution `q`. This is the algebraic heart of the redundancy-capacity
  theorem.
* `exists_source_redundancy_ge_mutualInfo` — **lower bound**: whatever code is
  used, some source in the class pays at least the mutual information `I(π)`
  of any prior `π`.
* `price_of_universality_upper` — **upper bound**: the Shannon code built from
  the mixture pays at most `log₂ |Θ| + 1` bits on *every* source of the class.
* `price_of_universality_sandwich` — for a class of `m` sources with pairwise
  disjoint supports the minimax redundancy is exactly `log₂ m`, up to one bit:
  `log₂ m ≤ minimax redundancy ≤ log₂ m + 1`.

The last statement is the promised closed form: the price of universality over
a class of `m` mutually distinguishable sources is `log₂ m` bits, i.e. exactly
the number of bits needed to name the source — no more and no less.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] {Θ : Type*} [Fintype Θ]

/-! ## Mixtures and mutual information -/






/-! ## The compensation identity -/


/-! ## The lower bound: universality costs at least the mutual information -/



/-! ## The upper bound: the mixture code -/




/-! ## Exact price for a class of mutually distinguishable sources -/

theorem PriceOfUniversality.price_of_universality_sandwich[Nonempty Θ] {p : Θ → A → ℝ}
    (hp : ∀ θ, IsPMF (p θ)) (hdisj : DisjointSupports p)
    (hcov : ∀ a : A, 0 < mixture (fun _ => (Fintype.card Θ : ℝ)⁻¹) p a) :
    (∀ L : A → ℕ, IsCode L → ∃ θ, logb 2 (Fintype.card Θ) ≤ redundancy (p θ) L) ∧
    (∃ L : A → ℕ, IsCode L ∧ ∀ θ, redundancy (p θ) L ≤ logb 2 (Fintype.card Θ) + 1) := by sorry

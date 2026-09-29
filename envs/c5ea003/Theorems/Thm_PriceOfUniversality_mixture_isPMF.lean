-- Prove2me | Theorems.Thm_PriceOfUniversality_mixture_isPMF
-- name    : PriceOfUniversality.mixture_isPMF
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:22:09.233966+00:00
-- url     : https://prove2.me/theorems/79b9d140-7d71-4ff2-a6d7-cfdf98e82e72
-- title:
--   Mixture isPMF
-- statement:
--   Formal statement of `PriceOfUniversality.mixture_isPMF` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PriceOfUniversality.mixture_isPMF{pri : Θ → ℝ} {p : Θ → A → ℝ} (hpri : IsPMF pri)
--       (hp : ∀ θ, IsPMF (p θ)) : IsPMF (mixture pri p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyMinimax.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyMinimax.lean#L50

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

theorem PriceOfUniversality.mixture_isPMF{pri : Θ → ℝ} {p : Θ → A → ℝ} (hpri : IsPMF pri)
    (hp : ∀ θ, IsPMF (p θ)) : IsPMF (mixture pri p) := by sorry

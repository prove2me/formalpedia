-- Prove2me | Theorems.Thm_PriceOfUniversality_kl_compensation
-- name    : PriceOfUniversality.kl_compensation
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:21:58.159204+00:00
-- url     : https://prove2.me/theorems/d99ae7b2-56a2-422f-8f0d-9c53a1ecb932
-- title:
--   Compensation identity (a Pythagorean decomposition for relative entropy):
-- statement:
--   **Compensation identity** (a Pythagorean decomposition for relative entropy):
--   for every coding distribution `q`, the average divergence of the class members
--   from `q` splits into the mutual information plus the divergence of the mixture
--   from `q`.
--
--   ```lean
--   theorem PriceOfUniversality.kl_compensation{pri : Θ → ℝ} {p : Θ → A → ℝ} {q : A → ℝ}
--       (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
--       (hq : ∀ a, 0 < q a) :
--       ∑ θ, pri θ * kl (p θ) q = mutualInfo pri p + kl (mixture pri p) q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyMinimax.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyMinimax.lean#L73

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

theorem PriceOfUniversality.kl_compensation{pri : Θ → ℝ} {p : Θ → A → ℝ} {q : A → ℝ}
    (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
    (hq : ∀ a, 0 < q a) :
    ∑ θ, pri θ * kl (p θ) q = mutualInfo pri p + kl (mixture pri p) q := by sorry

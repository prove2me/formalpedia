-- Prove2me | Theorems.Thm_BonferroniMarginals_sq_le_mul_add_of_le
-- name    : BonferroniMarginals.sq_le_mul_add_of_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:26:11.760753+00:00
-- url     : https://prove2.me/theorems/44ac9fd0-a09b-4481-8e80-66a86f0e7cb1
-- title:
--   Monotonicity of `S ↦ S²/(S+c)` in the division-free form needed below:
-- statement:
--   Monotonicity of `S ↦ S²/(S+c)` in the division-free form needed below:
--   if `S² ≤ N·(S+c)` and `u ≤ S`, then already `u² ≤ N·(u+c)`.
--
--   ```lean
--   theorem BonferroniMarginals.sq_le_mul_add_of_le{N S u c : ℕ} (h : S ^ 2 ≤ N * (S + c)) (hu : u ≤ S) :
--       u ^ 2 ≤ N * (u + c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BonferroniMarginals/Corradi.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BonferroniMarginals/Corradi.lean#L46

-- Thm stub generated from MachineLearning/BonferroniMarginals/Corradi.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity

/-!
# Which marginals? The Corrádi bound and the Fisher-type consequence

`Core.lean` develops the Bonferroni machinery for an *arbitrary* finite family;
the content of the conjecture is therefore entirely in **which marginals are fed
into it**.  This file feeds in the two standard hypotheses of design theory and
of ensemble learning:

* a uniform lower bound `m ≤ |Aᵢ|` on the **first** marginals, and
* a uniform upper bound `|Aᵢ ∩ Aⱼ| ≤ t` (`i ≠ j`) on the **second** marginals,

and extracts the sharp conclusions.

Main results.

* `card_cover_corradi` — **Corrádi's inequality**, division-free:
  `k·m² ≤ |cover| · (m + (k−1)·t)`, where `k` is the number of sets.
  Equivalently `|⋃ᵢ Aᵢ| ≥ k m² / (m + (k−1) t)`.
* `fisher_type_bound` — turning the same data around: if the ambient union is
  small (`N·t < m²`) then the *number of sets* is bounded,
  `k · (m² − N·t) ≤ N · (m − t)`.  This is the counting principle behind Fisher's
  inequality and behind Plotkin-type bounds in coding theory.
* `corradi_tight_of_pairwiseDisjoint`, `corradi_tight_of_constant` — the bound is
  attained at *both* extremes of the correlation scale (`t = 0` partitions and
  `t = m` totally correlated families), so no better bound is expressible in the
  marginal data `(k, m, t)` alone.
* `ensemble_coverage_bound` — the machine-learning reading: `k` hypotheses each
  failing on at least `m` of `N` samples, with pairwise co-failure at most `t`,
  must jointly fail on many distinct samples.

The proof route is: `sq_sum_card_le_card_cover_mul_sum_prod` (Cauchy–Schwarz on
the multiplicity function) + monotonicity of `S ↦ S²/(S+c)` + the marginal
hypotheses.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## Two arithmetic lemmas -/

theorem BonferroniMarginals.sq_le_mul_add_of_le{N S u c : ℕ} (h : S ^ 2 ≤ N * (S + c)) (hu : u ≤ S) :
    u ^ 2 ≤ N * (u + c) := by sorry

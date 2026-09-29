-- Prove2me | Theorems.Thm_PriceOfUniversality_exists_shtarkov_mul_le
-- name    : PriceOfUniversality.exists_shtarkov_mul_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:23:21.04349+00:00
-- url     : https://prove2.me/theorems/630c1114-98d5-4d91-aa64-b5dfa1435cfc
-- title:
--   Multiplicative form of the converse: every sub-probability weighting `q` is
-- statement:
--   Multiplicative form of the converse: every sub-probability weighting `q` is
--   beaten by a factor of at least `S` somewhere.
--
--   ```lean
--   theorem PriceOfUniversality.exists_shtarkov_mul_le{p : Θ → A → ℝ} {q : A → ℝ} (hp : ∀ θ, IsPMF (p θ))
--       (hq1 : ∑ a, q a ≤ 1) :
--       ∃ (θ : Θ) (a : A), shtarkov p * q a ≤ p θ a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyShtarkov.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyShtarkov.lean#L120

-- Thm stub generated from Novelty/UniversalRedundancyShtarkov.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
/-
# The price of universality, III: the exact minimax regret (Shtarkov sum)

The average-case analysis of `UniversalRedundancyMinimax` prices universality by
the mutual information of a prior.  Here we compute the **worst-case** (pointwise)
price *exactly*, with no `± 1` slack and no prior: for a finite class of sources
`{p θ}` on a finite alphabet the minimax pointwise regret is

  `log₂ S`,   where   `S = ∑ a, max_θ (p θ a)`

is the **Shtarkov sum** of the class, and the optimum is attained by the
normalised maximum likelihood (NML) distribution `nml p a = (max_θ p θ a) / S`.

Main results:

* `nml_regret_le` / `nml_isPMF` — achievability: NML never loses more than
  `log₂ S` bits against the best member of the class, on any message.
* `exists_regret_ge_logb_shtarkov` — converse: every coding distribution loses at
  least `log₂ S` bits on some message against some member of the class.
* `minimax_regret_eq_logb_shtarkov` — the two halves combined: the exact minimax
  regret.
* `code_regret_ge_logb_shtarkov` — the same converse stated for genuine integer
  code lengths satisfying Kraft's inequality.
* `shtarkov_disjointSupports` — `S = m` for `m` perfectly distinguishable
  sources, so the exact price of universality there is `log₂ m` bits.
* `one_le_shtarkov` — universality never helps: `S ≥ 1`, i.e. the regret is
  always nonnegative.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] [Nonempty A] {Θ : Type*} [Fintype Θ] [Nonempty Θ]

/-! ## The Shtarkov sum and the NML distribution -/










/-! ## Achievability: NML pays at most `log₂ S` -/



/-! ## Converse: no coding distribution can pay less than `log₂ S` -/

theorem PriceOfUniversality.exists_shtarkov_mul_le{p : Θ → A → ℝ} {q : A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (hq1 : ∑ a, q a ≤ 1) :
    ∃ (θ : Θ) (a : A), shtarkov p * q a ≤ p θ a := by sorry

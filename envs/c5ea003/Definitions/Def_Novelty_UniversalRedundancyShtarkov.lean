-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyShtarkov
-- name    : Novelty_UniversalRedundancyShtarkov
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:45:48.425631+00:00
-- url     : https://prove2.me/theorems/d732f724-e631-4ace-9e40-4f68a3479d6f
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyShtarkov
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyShtarkov`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyShtarkov.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyMinimax
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

namespace PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] [Nonempty A] {Θ : Type*} [Fintype Θ] [Nonempty Θ]

/-! ## The Shtarkov sum and the NML distribution -/

/-- The maximum likelihood of the message `a` over the class. -/
noncomputable def maxLik (p : Θ → A → ℝ) (a : A) : ℝ :=
  (univ : Finset Θ).sup' univ_nonempty (fun θ => p θ a)

/-- The **Shtarkov sum** of a class of sources: `∑ a max_θ p θ a`. Its logarithm is
the exact minimax regret of the class. -/
noncomputable def shtarkov (p : Θ → A → ℝ) : ℝ := ∑ a, maxLik p a

/-- The normalised maximum likelihood (Shtarkov) distribution. -/
noncomputable def nml (p : Θ → A → ℝ) : A → ℝ := fun a => maxLik p a / shtarkov p







/-! ## Achievability: NML pays at most `log₂ S` -/



/-! ## Converse: no coding distribution can pay less than `log₂ S` -/





/-! ## The exact price for perfectly distinguishable sources -/



end PriceOfUniversality



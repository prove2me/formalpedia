-- Prove2me | solution 1 for PriceOfUniversality.nml_logb_regret_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:17:49.93687+00:00
-- url     : https://prove2.me/submissions/0047df5d-ece6-4625-b70a-2f44c245f8ad

-- Sol generated from Novelty/UniversalRedundancyShtarkov.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_nml_regret_le
import Theorems.Thm_PriceOfUniversality_one_le_shtarkov
import Theorems.Thm_PriceOfUniversality_shtarkov_pos
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





/-! ## The exact price for perfectly distinguishable sources -/




open PriceOfUniversality in
omit [Nonempty A] in
theorem solution{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (hpos : ∀ a, 0 < maxLik p a) (θ : Θ) (a : A) :
    logb 2 (p θ a / nml p a) ≤ logb 2 (shtarkov p) := by
  have hS := shtarkov_pos hp
  have hnml : 0 < nml p a := div_pos (hpos a) hS
  have hratio : p θ a / nml p a ≤ shtarkov p := by
    rw [div_le_iff₀ hnml]
    have := nml_regret_le hp θ a
    linarith [this]
  rcases le_or_gt (p θ a / nml p a) 0 with h | h
  · have hzero : p θ a / nml p a = 0 :=
      le_antisymm h (div_nonneg ((hp θ).nonneg a) hnml.le)
    rw [hzero, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) (one_le_shtarkov hp)
  · exact Real.logb_le_logb_of_le (by norm_num) h hratio

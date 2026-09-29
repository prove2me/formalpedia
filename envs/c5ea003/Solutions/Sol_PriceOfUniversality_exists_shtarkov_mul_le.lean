-- Prove2me | solution 1 for PriceOfUniversality.exists_shtarkov_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:56:26.580525+00:00
-- url     : https://prove2.me/submissions/26a7ea4a-b684-4693-a71c-e61c97fb8857

-- Sol generated from Novelty/UniversalRedundancyShtarkov.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
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
theorem solution{p : Θ → A → ℝ} {q : A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (hq1 : ∑ a, q a ≤ 1) :
    ∃ (θ : Θ) (a : A), shtarkov p * q a ≤ p θ a := by
  by_contra hcon
  push_neg at hcon
  have hmax : ∀ a : A, maxLik p a < shtarkov p * q a := by
    intro a
    refine (Finset.sup'_lt_iff univ_nonempty).2 ?_
    intro θ _
    exact hcon θ a
  have hlt : shtarkov p < ∑ a, shtarkov p * q a := by
    have := Finset.sum_lt_sum_of_nonempty (univ_nonempty (α := A)) (fun a _ => hmax a)
    simpa [shtarkov] using this
  have hle : ∑ a, shtarkov p * q a ≤ shtarkov p := by
    rw [← Finset.mul_sum]
    calc shtarkov p * ∑ a, q a ≤ shtarkov p * 1 :=
          mul_le_mul_of_nonneg_left hq1 (shtarkov_pos hp).le
      _ = shtarkov p := mul_one _
  linarith

-- Prove2me | solution 1 for PriceOfUniversality.code_regret_ge_logb_shtarkov
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:58:12.59371+00:00
-- url     : https://prove2.me/submissions/d72a3de5-f447-432a-9071-4553640ffb22

-- Sol generated from Novelty/UniversalRedundancyShtarkov.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_exists_shtarkov_mul_le
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


/-- Logarithmic form of the converse: for every strictly positive coding
distribution `q` of total mass at most one there is a message on which some member
of the class beats `q` by at least `log₂ S` bits. -/
theorem exists_regret_ge_logb_shtarkov {p : Θ → A → ℝ} {q : A → ℝ}
    (hp : ∀ θ, IsPMF (p θ)) (hq : ∀ a, 0 < q a) (hq1 : ∑ a, q a ≤ 1) :
    ∃ (θ : Θ) (a : A), logb 2 (shtarkov p) ≤ logb 2 (p θ a / q a) := by
  obtain ⟨θ, a, hθa⟩ := exists_shtarkov_mul_le hp hq1
  refine ⟨θ, a, ?_⟩
  have hle : shtarkov p ≤ p θ a / q a := by
    rw [le_div_iff₀ (hq a)]
    linarith [hθa]
  exact Real.logb_le_logb_of_le (by norm_num) (shtarkov_pos hp) hle



/-! ## The exact price for perfectly distinguishable sources -/




open PriceOfUniversality in
theorem solution{p : Θ → A → ℝ} {L : A → ℕ}
    (hp : ∀ θ, IsPMF (p θ)) (hL : IsCode L) :
    ∃ (θ : Θ) (a : A), logb 2 (shtarkov p) ≤ (L a : ℝ) + logb 2 (p θ a) := by
  obtain ⟨θ, a, hθa⟩ :=
    exists_regret_ge_logb_shtarkov (q := fun a => ((2:ℝ)⁻¹) ^ (L a)) hp
      (fun a => by positivity) hL
  refine ⟨θ, a, le_trans hθa ?_⟩
  rcases eq_or_lt_of_le ((hp θ).nonneg a) with h | h
  · -- a zero-probability message: `logb 0 = 0` by convention, and lengths are nonnegative
    have hz : p θ a / ((2:ℝ)⁻¹) ^ (L a) = 0 := by rw [← h]; simp
    rw [hz, ← h]
    simp
  · have hpow : (0:ℝ) < ((2:ℝ)⁻¹) ^ (L a) := by positivity
    rw [Real.logb_div (ne_of_gt h) (ne_of_gt hpow)]
    have hL2 : logb 2 (((2:ℝ)⁻¹) ^ (L a)) = -(L a : ℝ) := by
      rw [Real.logb_pow, Real.logb_inv]; simp
    rw [hL2]; linarith

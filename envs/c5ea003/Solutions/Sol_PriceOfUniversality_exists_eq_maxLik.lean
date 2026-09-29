-- Prove2me | solution 1 for PriceOfUniversality.exists_eq_maxLik
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:58:13.138823+00:00
-- url     : https://prove2.me/submissions/60cf61c1-6c5b-4d65-899a-bfeb5c5a10dd

-- Sol generated from Novelty/UniversalRedundancyShtarkov.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_le_maxLik
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
omit [Fintype A] [Nonempty A] in
theorem solution(p : Θ → A → ℝ) (a : A) : ∃ θ : Θ, maxLik p a = p θ a := by
  obtain ⟨θ₀, -, hθ₀⟩ :=
    Finset.exists_max_image (univ : Finset Θ) (fun θ => p θ a) univ_nonempty
  exact ⟨θ₀, le_antisymm
    ((Finset.sup'_le_iff univ_nonempty _).2 fun θ _ => hθ₀ θ (mem_univ θ))
    (le_maxLik p θ₀ a)⟩

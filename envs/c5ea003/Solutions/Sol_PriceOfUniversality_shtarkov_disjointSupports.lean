-- Prove2me | solution 1 for PriceOfUniversality.shtarkov_disjointSupports
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:05:25.748584+00:00
-- url     : https://prove2.me/submissions/a3262c70-e80d-4305-aa75-069788bfd324

-- Sol generated from Novelty/UniversalRedundancyShtarkov.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
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
omit [Nonempty A] in
theorem solution{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (hdisj : DisjointSupports p) :
    shtarkov p = Fintype.card Θ := by
  have hmax : ∀ a : A, maxLik p a = ∑ θ, p θ a := by
    intro a
    obtain ⟨θ₀, -, hθ₀⟩ :=
      Finset.exists_max_image (univ : Finset Θ) (fun θ => p θ a) univ_nonempty
    have hml : maxLik p a = p θ₀ a := by
      refine le_antisymm ?_ (le_maxLik p θ₀ a)
      exact (Finset.sup'_le_iff univ_nonempty _).2 fun θ _ => hθ₀ θ (mem_univ θ)
    rw [hml]
    rcases eq_or_lt_of_le ((hp θ₀).nonneg a) with h | h
    · -- no source gives `a` positive probability
      have hall : ∀ θ : Θ, p θ a = 0 := by
        intro θ
        have h1 := hθ₀ θ (mem_univ θ)
        have h2 := (hp θ).nonneg a
        have h3 : p θ₀ a = 0 := h.symm
        linarith
      simp [hall]
    · symm
      refine Finset.sum_eq_single θ₀ ?_ ?_
      · intro θ _ hne
        exact hdisj θ₀ θ a (Ne.symm hne) h
      · intro hcon; exact absurd (mem_univ θ₀) hcon
  calc shtarkov p = ∑ a, ∑ θ, p θ a := Finset.sum_congr rfl fun a _ => hmax a
    _ = ∑ _θ : Θ, (1:ℝ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun θ _ => (hp θ).total
    _ = Fintype.card Θ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_one]

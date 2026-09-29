-- Prove2me | solution 1 for PriceOfUniversality.shtarkov_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:22:33.579133+00:00
-- url     : https://prove2.me/submissions/1cd084fa-448d-4d80-80f6-56e0c64c3cb1

-- Sol generated from Novelty/UniversalRedundancyTotalVariation.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Definitions.Def_Novelty_UniversalRedundancyTotalVariation
import Theorems.Thm_PriceOfUniversality_le_maxLik
/-
# The price of universality, X: an exact closed form for two sources

The rigidity theorem of `UniversalRedundancyRigidity.lean` says the price of
universality measures distinguishability rather than cardinality.  For a class of
**two** sources we can say exactly how:

  `S({p₀, p₁}) = 1 + TV(p₀, p₁)`,

`TV` the total variation distance, so the exact minimax regret is

  `log₂ (1 + TV(p₀, p₁))`  bits,

interpolating continuously between `0` bits for identical sources and `1` bit —
the cost of naming the source — for perfectly distinguishable ones.  This is the
first *closed form* in the programme: the price of universality of a two-element
class is a metric quantity.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A]


omit [Fintype A] in
/-- For a two-element class the maximum likelihood is the pointwise maximum. -/
theorem maxLik_fin_two (p : Fin 2 → A → ℝ) (a : A) :
    maxLik p a = max (p 0 a) (p 1 a) := by
  refine le_antisymm ((Finset.sup'_le_iff univ_nonempty _).2 fun θ _ => ?_) ?_
  · fin_cases θ
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_maxLik p 0 a) (le_maxLik p 1 a)








open PriceOfUniversality in
theorem solution{p : Fin 2 → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) :
    shtarkov p = 1 + tv p := by
  have hmax : ∀ a : A, maxLik p a = (p 0 a + p 1 a + |p 0 a - p 1 a|) / 2 := by
    intro a
    rw [maxLik_fin_two]
    rcases le_total (p 0 a) (p 1 a) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
  calc shtarkov p = ∑ a, (p 0 a + p 1 a + |p 0 a - p 1 a|) / 2 :=
        Finset.sum_congr rfl fun a _ => hmax a
    _ = ((∑ a, p 0 a) + (∑ a, p 1 a) + ∑ a, |p 0 a - p 1 a|) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = 1 + tv p := by rw [(hp 0).total, (hp 1).total, tv]; ring

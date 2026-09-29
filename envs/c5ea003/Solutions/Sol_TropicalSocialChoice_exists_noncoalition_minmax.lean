-- Prove2me | solution 1 for TropicalSocialChoice.exists_noncoalition_minmax
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T05:59:23.133198+00:00
-- url     : https://prove2.me/submissions/2bc53314-3331-4308-8854-9d698d9dd9ab

import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceSemiring

open TropicalSocialChoice Abstract MinMax Finset in
theorem solution {α : Type*} [LinearOrder α] [BoundedOrder α] {c : MinMax α} (hb : ⊥ < c)
    (ht : c < ⊤) :
    ∃ f : (Fin 2 → MinMax α) → MinMax α,
      IsSLinear f ∧ SPareto f ∧ SDiagIdem f ∧ ∀ s : Finset (Fin 2), f ≠ sCoalition s := by
  -- the rule `x ↦ min (max c x₀) x₁`
  let a : Fin 2 → MinMax α := ![c, 1]
  refine ⟨fun x => SForm a x, ⟨a, fun x => rfl⟩, ?_, ?_, ?_⟩
  · intro t
    simp only [SForm, Fin.sum_univ_two]
    show (c * t + 1 * t : MinMax α) = t
    rw [one_mul]
    show (c ⊔ t) ⊓ t = t
    exact inf_eq_right.2 le_sup_right
  · intro x
    have hx : x * x = x := funext fun i => by
      rw [Pi.mul_apply, MinMax.mul_def, sup_idem]
    simp only
    rw [hx, MinMax.mul_def, sup_idem]
  · intro s hs
    have h1 := congrFun hs ![⊥, ⊤]
    have hv : SForm a ![⊥, ⊤] = c := by
      simp only [SForm, Fin.sum_univ_two]
      show (c ⊔ ⊥) ⊓ ((⊥ : MinMax α) ⊔ ⊤) = c
      simp
    simp only at h1
    rw [hv] at h1
    by_cases h0 : (0 : Fin 2) ∈ s
    · have h2 : sCoalition s ![⊥, ⊤] = (⊥ : MinMax α) := by
        unfold sCoalition
        rw [← Finset.add_sum_erase s _ h0]
        show (⊥ : MinMax α) ⊓ _ = ⊥
        exact bot_inf_eq _
      rw [h2] at h1
      exact hb.ne' h1
    · have h2 : sCoalition s ![⊥, ⊤] = (0 : MinMax α) := by
        unfold sCoalition
        refine Finset.sum_eq_zero fun i hi => ?_
        fin_cases i
        · exact absurd hi h0
        · rfl
      rw [h2] at h1
      exact ht.ne h1

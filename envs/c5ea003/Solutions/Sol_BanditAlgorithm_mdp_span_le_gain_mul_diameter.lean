-- Prove2me | solution 1 for BanditAlgorithm.mdp_span_le_gain_mul_diameter
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T04:51:03.833526+00:00
-- url     : https://prove2.me/submissions/cddfb77a-25d8-4a93-a0ce-68e475190e2a

import Theorems.Thm_BanditAlgorithm_mdp_value_diff_le_travel_time

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
The diameter is the maximum over pairs of states of the minimum over policies
of the travel time, so bounding the difference of values by the travel time of
one policy, for the minimising policy, bounds the span by the diameter.
-/

variable {S A : ℕ}

/-- **Lemma 38.3** (L&S; Exercise 38.13).  For a solution `(ρ, v)` of the
Bellman optimality inequality on an MDP of finite diameter,
`span(v) ≤ ρ · D(M)`.  With `ρ = ρ* ≤ 1` this is the bound `span(v) ≤ D(M)`
used in Step 2 of the proof of Theorem 38.6. -/
theorem solution (M : FiniteMDP S A) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (v : Fin S → ℝ) (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s)
    (hD : mdpDiameterENN M ≠ ⊤) (s s' : Fin S) :
    v s - v s' ≤ ρ * mdpDiameter M := by
  rcases eq_or_ne s s' with rfl | hne
  · have : (0 : ℝ) ≤ mdpDiameter M := ENNReal.toReal_nonneg
    simpa using mul_nonneg hρ this
  · -- the infimum over policies of the travel time from `s'` to `s`
    have hle : (⨅ f : Fin S → Fin A, mdpTravelTime M f s' s) ≤ mdpDiameterENN M := by
      refine le_iSup_of_le s' (le_iSup_of_le s (le_iSup_of_le hne.symm le_rfl))
    have hinf_ne : (⨅ f : Fin S → Fin A, mdpTravelTime M f s' s) ≠ ⊤ :=
      fun hcon ↦ hD (top_le_iff.mp (hcon ▸ hle))
    have hnonempty : Nonempty (Fin S → Fin A) := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      exact hinf_ne (iInf_of_empty _)
    obtain ⟨f₀, hf₀⟩ := Finite.exists_min (fun f : Fin S → Fin A ↦ mdpTravelTime M f s' s)
    have hattain : (⨅ f : Fin S → Fin A, mdpTravelTime M f s' s)
        = mdpTravelTime M f₀ s' s :=
      le_antisymm (iInf_le _ f₀) (le_iInf hf₀)
    have hfin : mdpTravelTime M f₀ s' s ≠ ⊤ := hattain ▸ hinf_ne
    calc v s - v s' ≤ ρ * (mdpTravelTime M f₀ s' s).toReal :=
          BanditAlgorithm.mdp_value_diff_le_travel_time M f₀ s' s ρ v lo hi hv hbell hfin
      _ ≤ ρ * mdpDiameter M := by
          refine mul_le_mul_of_nonneg_left ?_ hρ
          rw [mdpDiameter, ← hattain]
          exact ENNReal.toReal_mono hD hle

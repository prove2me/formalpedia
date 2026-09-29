-- Prove2me | solution 1 for mme_stothers_phi224_normalized_marginal_orbit_averages
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:51:22.972723+00:00
-- url     : https://prove2.me/submissions/8c2d988a-000d-4173-8196-b380ac34325b

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_marginal_orbit_averages

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N) (x : Fin 9 → ℝ)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      (∑ r : Fin 9,
        if MME.StothersFourth.Phi224.pattern r i = s then x r else 0) =
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ) / ((2 * N : ℕ) : ℝ)) :
    (x 0 + x 8) / 2 =
        (alpha : ℝ) / ((2 * N : ℕ) : ℝ) ∧
      (x 1 + x 3 + x 5 + x 7) / 4 =
        (beta : ℝ) / ((2 * N : ℕ) : ℝ) ∧
      (x 2 + x 6) / 2 =
        (gamma : ℝ) / ((2 * N : ℕ) : ℝ) ∧
      x 4 = ((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) := by
  let D : ℝ := ((2 * N : ℕ) : ℝ)
  have hD : D ≠ 0 := by
    dsimp [D]
    positivity
  let y : Fin 9 → ℝ := fun r ↦ D * x r
  have hymarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      (∑ r : Fin 9,
        if MME.StothersFourth.Phi224.pattern r i = s then y r else 0) =
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ) := by
    intro i s
    calc
      (∑ r : Fin 9,
          if MME.StothersFourth.Phi224.pattern r i = s then y r else 0) =
          D * ∑ r : Fin 9,
            if MME.StothersFourth.Phi224.pattern r i = s then x r else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp only [y]
        split_ifs <;> ring
      _ = D *
          ((MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ) / D) := by
        rw [hmarginal]
      _ = (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ) := by
        field_simp
  obtain ⟨ha, hb, hc, hd⟩ :=
    mme_stothers_phi224_marginal_orbit_averages
      alpha beta gamma delta y hymarginal
  constructor
  · dsimp only [y] at ha
    change (x 0 + x 8) / 2 = (alpha : ℝ) / D
    field_simp [hD] at ha ⊢
    linarith
  constructor
  · dsimp only [y] at hb
    change (x 1 + x 3 + x 5 + x 7) / 4 = (beta : ℝ) / D
    field_simp [hD] at hb ⊢
    linarith
  constructor
  · dsimp only [y] at hc
    change (x 2 + x 6) / 2 = (gamma : ℝ) / D
    field_simp [hD] at hc ⊢
    linarith
  · dsimp only [y] at hd
    change x 4 = ((2 * delta : ℕ) : ℝ) / D
    field_simp [hD] at hd ⊢
    norm_num at hd ⊢
    exact hd

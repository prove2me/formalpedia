-- Prove2me | solution 1 for DAREx.CoefficientEnergyIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T22:08:51.843325+00:00
-- url     : https://prove2.me/submissions/ac3f10aa-19ec-4cca-936c-03bc861a7e2a

import Definitions.Def_DAREx_Model
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators
open DAREx

-- Deng et al., Appendix E.1, PDF p. 31, unnumbered coefficient-energy identity.
theorem solution :
    ∀ (n : ℕ) (c : Fin n → ℝ), 0 < n →
      energy c = (n : ℝ) * (empiricalMean c ^ 2 + empiricalVariance c) := by
  intro n c hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold empiricalVariance empiricalMean coefficientSum energy
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

-- Prove2me | Definitions.Def_Nonadditivity_StrictEntropy
-- name    : Nonadditivity_StrictEntropy
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:33.950335+00:00
-- url     : https://prove2.me/theorems/01332fdb-76d8-4791-b3f4-6c54105effd1
-- title:
--   Strict entropy deficit away from the maximally mixed state
-- statement:
--   For a density matrix $\rho$ on a nonempty finite complex space of dimension $d$, $\rho\ne I_d/d$ implies $S(\rho)<\log d$. The bundle proves the equality characterization and the analogous strict Shannon entropy inequality for nonuniform finite probability weights. Entropy here is measured with natural logarithms.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/StrictEntropy.lean#L16-L90

import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! # Strictness of the finite-dimensional entropy maximum -/

noncomputable section

namespace Nonadditivity.Entropy

open scoped BigOperators Matrix ComplexOrder

theorem shannon_lt_log_card_of_not_uniform {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hne : ∃ i, p i ≠ 1 / (Fintype.card ι : ℝ)) :
    shannon p < Real.log (Fintype.card ι) := by
  classical
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by
    change (0 : ℝ) < Fintype.card ι
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hterm (i : ι) : p i - 1 / d - p i * Real.log d ≤ p i * Real.log (p i) := by
    by_cases hz : p i = 0
    · simp only [hz, zero_sub, zero_mul, sub_zero]
      exact neg_nonpos.mpr (le_of_lt (div_pos zero_lt_one hd))
    · have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      have hlog := Real.one_sub_inv_le_log_of_pos (mul_pos hd hi)
      rw [Real.log_mul hd.ne' hz] at hlog
      have hm := mul_le_mul_of_nonneg_left hlog (hp i)
      have hfrac : p i * (1 - (d * p i)⁻¹) = p i - 1 / d := by field_simp
      rw [hfrac] at hm
      nlinarith
  obtain ⟨i, hi⟩ := hne
  have hstrict : p i - 1 / d - p i * Real.log d < p i * Real.log (p i) := by
    by_cases hz : p i = 0
    · simp only [hz, zero_sub, zero_mul, sub_zero]
      exact neg_lt_zero.mpr (div_pos zero_lt_one hd)
    · have hip : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      have hmne : (d * p i)⁻¹ ≠ 1 := by
        intro h
        have hh : d * p i = 1 := inv_eq_one.mp h
        apply hi
        change p i = 1 / d
        apply (eq_div_iff hd.ne').mpr
        simpa [mul_comm] using hh
      have hlog := Real.log_lt_sub_one_of_pos (inv_pos.mpr (mul_pos hd hip)) hmne
      rw [Real.log_inv, Real.log_mul hd.ne' hz] at hlog
      have hm := mul_lt_mul_of_pos_left hlog hip
      have hfrac : p i * ((d * p i)⁻¹ - 1) = 1 / d - p i := by field_simp
      rw [hfrac] at hm
      nlinarith
  have hsumterm := Finset.sum_lt_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    ⟨i, Finset.mem_univ i, hstrict⟩
  have hleft : (∑ i, (p i - 1 / d - p i * Real.log d)) = -Real.log d := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, one_mul]
    change 1 - d * (1 / d) - Real.log d = -Real.log d
    field_simp
    ring
  rw [hleft] at hsumterm
  unfold shannon
  change _ < Real.log d
  linarith

theorem DensityMatrix.eq_maximallyMixed_of_weights_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι)
    (h : ∀ i, ρ.weights i = 1 / (Fintype.card ι : ℝ)) :
    ρ = maximallyMixed ι := by
  apply DensityMatrix.ext
  rw [ρ.positive.isHermitian.spectral_theorem]
  have hd : Matrix.diagonal (fun i => (ρ.weights i : ℂ)) =
      ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    simp only [h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  change Unitary.conjStarAlgAut ℂ _ _ (Matrix.diagonal (fun i => (ρ.weights i : ℂ))) = _
  rw [hd, map_smul, map_one]
  rfl

theorem DensityMatrix.vonNeumann_lt_log_card_of_ne_maximallyMixed
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι)
    (hne : ρ ≠ maximallyMixed ι) :
    ρ.vonNeumann < Real.log (Fintype.card ι) := by
  apply shannon_lt_log_card_of_not_uniform ρ.weights ρ.weights_nonneg ρ.weights_sum
  by_contra h
  push_neg at h
  exact hne (ρ.eq_maximallyMixed_of_weights_eq h)

end Nonadditivity.Entropy



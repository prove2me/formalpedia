-- Prove2me | solution 1 for ExtendedSmale9.lemma_11_1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:21:22.566883+00:00
-- url     : https://prove2.me/submissions/8b18c18f-9650-42b5-8763-509b9e1e29f6

import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ExtendedSmale9 Matrix

namespace CSmale

def i0 {N : ℕ} (hN : 3 ≤ N) : Fin N := ⟨0, by omega⟩
def i1 {N : ℕ} (hN : 3 ≤ N) : Fin N := ⟨1, by omega⟩
def i2 {N : ℕ} (hN : 3 ≤ N) : Fin N := ⟨2, by omega⟩

def pair {N : ℕ} (hN : 3 ≤ N) (u v : ℝ) : Fin N → ℝ :=
  Pi.single (i0 hN) u + Pi.single (i1 hN) v

theorem pair_apply {N : ℕ} (hN : 3 ≤ N) (u v : ℝ) (j : Fin N) :
    pair hN u v j = if (j : ℕ) = 0 then u else if (j : ℕ) = 1 then v else 0 := by
  by_cases h0 : (j : ℕ) = 0
  · simp [pair, Pi.single_apply, i0, i1, Fin.ext_iff, h0]
  · by_cases h1 : (j : ℕ) = 1
    · simp [pair, Pi.single_apply, i0, i1, Fin.ext_iff, h0, h1]
    · simp [pair, Pi.single_apply, i0, i1, Fin.ext_iff, h0, h1, Ne.symm h0, Ne.symm h1]

theorem pair_cost {N : ℕ} (hN : 3 ≤ N) (u v : ℝ) :
    (fun _ : Fin N => (1 : ℝ)) ⬝ᵥ pair hN u v = u + v := by
  simp [pair, dotProduct_add, dotProduct_single]

theorem pair_feasible {m N : ℕ} (hN : 3 ≤ N) (α β y u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (heq : α * u + β * v = y) :
    pair hN u v ∈ lpFeasible (lpVectorA y m) (lpMatrixA α β m N) := by
  constructor
  · unfold pair
    rw [Matrix.mulVec_add, Matrix.mulVec_single, Matrix.mulVec_single]
    funext i
    simp only [Pi.add_apply, lpMatrixA, i0, i1, lpVectorA]
    by_cases hi : (i : ℕ) = 0
    · simpa [lpMatrixA, hi] using heq
    · simp [lpMatrixA, hi, show ¬ (0 : ℕ) = i.val + 2 by omega, show ¬ (1 : ℕ) = i.val + 2 by omega]
  · intro j
    rw [pair_apply]
    split_ifs <;> positivity

theorem row_zero {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y : ℝ)
    (z : Fin N → ℝ) (hz : z ∈ lpFeasible (lpVectorA y m) (lpMatrixA α β m N)) :
    α * z (i0 hN) + β * z (i1 hN) - z (i2 hN) = y := by
  have hrow : (lpMatrixA α β m N) ⟨0, by omega⟩ =
      Pi.single (i0 hN) α + Pi.single (i1 hN) β + Pi.single (i2 hN) (-1) := by
    funext j
    simp only [lpMatrixA, if_pos rfl, Pi.add_apply]
    by_cases h0 : (j : ℕ) = 0
    · simp [Pi.single_apply, i0, i1, i2, Fin.ext_iff, h0]
    · by_cases h1 : (j : ℕ) = 1
      · simp [Pi.single_apply, i0, i1, i2, Fin.ext_iff, h0, h1]
      · by_cases h2 : (j : ℕ) = 2
        · simp [Pi.single_apply, i0, i1, i2, Fin.ext_iff, h0, h1, h2]
        · simp [Pi.single_apply, i0, i1, i2, Fin.ext_iff, h0, h1, h2, Ne.symm h0, Ne.symm h1, Ne.symm h2]
  have h := congrFun hz.1 (⟨0, by omega⟩ : Fin m)
  change ((lpMatrixA α β m N) ⟨0, by omega⟩) ⬝ᵥ z = y at h
  rw [hrow, add_dotProduct, add_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct] at h
  linarith

theorem two_le_sum {N : ℕ} (hN : 3 ≤ N) (z : Fin N → ℝ) (hz : ∀ j, 0 ≤ z j) :
    z (i0 hN) + z (i1 hN) ≤ ∑ j, z j := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := z)
    (Finset.subset_univ ({i0 hN, i1 hN} : Finset (Fin N))) (fun j _ _ => hz j)
  simpa [Finset.sum_pair, show i0 hN ≠ i1 hN by simp [i0, i1, Fin.ext_iff]] using h

theorem lower_bound {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (z : Fin N → ℝ)
    (hz : z ∈ lpFeasible (lpVectorA y m) (lpMatrixA α β m N)) :
    y / max α β ≤ (fun _ : Fin N => (1 : ℝ)) ⬝ᵥ z := by
  have hmpos : 0 < max α β := hα.trans_le (le_max_left _ _)
  have hsum := two_le_sum hN z hz.2
  have hrow := row_zero hm hN α β y z hz
  have h0 := mul_le_mul_of_nonneg_right (le_max_left α β) (hz.2 (i0 hN))
  have h1 := mul_le_mul_of_nonneg_right (le_max_right α β) (hz.2 (i1 hN))
  have hs := mul_le_mul_of_nonneg_left hsum hmpos.le
  simp only [dotProduct, one_mul]
  apply (div_le_iff₀ hmpos).mpr
  nlinarith [hz.2 (i2 hN)]

theorem pair_optimal {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y u v : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (heq : α * u + β * v = y) (hcost : u + v = y / max α β) :
    pair hN u v ∈ lpArgmin (fun _ => 1) (lpVectorA y m) (lpMatrixA α β m N) := by
  refine ⟨pair_feasible hN α β y u v hu hv heq, fun z hz => ?_⟩
  rw [pair_cost, hcost]
  exact lower_bound hm hN α β y hα hβ z hz

theorem optimal_cost {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hy : 0 < y) (z : Fin N → ℝ)
    (hz : z ∈ lpArgmin (fun _ => 1) (lpVectorA y m) (lpMatrixA α β m N)) :
    (∑ j, z j) = y / max α β := by
  have hlo := lower_bound hm hN α β y hα hβ z hz.1
  simp only [dotProduct, one_mul] at hlo
  apply le_antisymm _ hlo
  by_cases hab : β ≤ α
  · have hf := pair_feasible (m := m) hN α β y (y / α) 0 (by positivity) le_rfl (by field_simp; ring)
    have hh := hz.2 _ hf
    rw [pair_cost] at hh
    simpa [dotProduct, max_eq_left hab] using hh
  · have hf := pair_feasible (m := m) hN α β y 0 (y / β) le_rfl (by positivity) (by field_simp; ring)
    have hh := hz.2 _ hf
    rw [pair_cost] at hh
    simpa [dotProduct, max_eq_right (le_of_not_ge hab)] using hh

end CSmale

namespace CSmale

theorem optimal_pair {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hy : 0 < y) (z : Fin N → ℝ)
    (hz : z ∈ lpArgmin (fun _ => 1) (lpVectorA y m) (lpMatrixA α β m N)) :
    z = pair hN (z (i0 hN)) (z (i1 hN)) ∧ α * z (i0 hN) + β * z (i1 hN) = y := by
  have hcost := optimal_cost hm hN α β y hα hβ hy z hz
  have hmax : 0 < max α β := hα.trans_le (le_max_left _ _)
  have hcost' : max α β * (∑ j, z j) = y := by rw [hcost]; field_simp
  have hrow := row_zero hm hN α β y z hz.1
  have hsum := two_le_sum hN z hz.1.2
  have hg0 : 0 ≤ (max α β - α) * z (i0 hN) := mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) (hz.1.2 _)
  have hg1 : 0 ≤ (max α β - β) * z (i1 hN) := mul_nonneg (sub_nonneg.mpr (le_max_right _ _)) (hz.1.2 _)
  have hremle : max α β * ((∑ j, z j) - z (i0 hN) - z (i1 hN)) ≤ 0 := by
    nlinarith [hz.1.2 (i2 hN)]
  have hrem0 : 0 ≤ (∑ j, z j) - z (i0 hN) - z (i1 hN) := by linarith
  have hrem : (∑ j, z j) = z (i0 hN) + z (i1 hN) := by
    have hh : max α β * ((∑ j, z j) - z (i0 hN) - z (i1 hN)) = 0 :=
      le_antisymm hremle (mul_nonneg hmax.le hrem0)
    have := (mul_eq_zero.mp hh).resolve_left hmax.ne'
    linarith
  have h01 : i0 hN ≠ i1 hN := by simp [i0, i1, Fin.ext_iff]
  have hzero : ∀ j : Fin N, j ≠ i0 hN → j ≠ i1 hN → z j = 0 := by
    intro j hj0 hj1
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := z)
      (Finset.subset_univ ({i0 hN, i1 hN, j} : Finset (Fin N))) (fun k _ _ => hz.1.2 k)
    have hh' : z (i0 hN) + z (i1 hN) + z j ≤ ∑ k, z k := by
      simpa [h01, hj0, hj1, Ne.symm hj0, Ne.symm hj1, add_assoc] using hh
    have := hz.1.2 j
    linarith
  constructor
  · funext j
    by_cases hj0 : j = i0 hN
    · subst j
      simp [pair, Pi.single_apply, h01, Ne.symm h01]
    · by_cases hj1 : j = i1 hN
      · subst j
        simp [pair, Pi.single_apply, h01, Ne.symm h01]
      · simp [pair, Pi.single_apply, hj0, hj1, Ne.symm hj0, Ne.symm hj1, hzero j hj0 hj1]
  · have hz2 := hzero (i2 hN) (by simp [i2, i0, Fin.ext_iff]) (by simp [i2, i1, Fin.ext_iff])
    linarith

end CSmale

namespace CSmale

theorem optimal_pair_sum {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hy : 0 < y) (z : Fin N → ℝ)
    (hz : z ∈ lpArgmin (fun _ => 1) (lpVectorA y m) (lpMatrixA α β m N)) :
    z (i0 hN) + z (i1 hN) = y / max α β := by
  have hshape := (optimal_pair hm hN α β y hα hβ hy z hz).1
  calc
    _ = (fun _ : Fin N => (1 : ℝ)) ⬝ᵥ pair hN (z (i0 hN)) (z (i1 hN)) := (pair_cost _ _ _).symm
    _ = (fun _ : Fin N => (1 : ℝ)) ⬝ᵥ z := congrArg _ hshape.symm
    _ = ∑ j, z j := by simp [dotProduct]
    _ = _ := optimal_cost hm hN α β y hα hβ hy z hz

theorem alpha_larger {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hy : 0 < y) (hab : β < α) :
    lpArgmin (fun _ => 1) (lpVectorA y m) (lpMatrixA α β m N) = {pair hN (y / max α β) 0} := by
  ext z
  constructor
  · intro hz
    obtain ⟨hshape, heq⟩ := optimal_pair hm hN α β y hα hβ hy z hz
    have hc := optimal_pair_sum hm hN α β y hα hβ hy z hz
    have hprod : α * (z (i0 hN) + z (i1 hN)) = y := by
      rw [hc, max_eq_left hab.le]
      field_simp
    have hgap : (α - β) * z (i1 hN) = 0 := by nlinarith
    have hv : z (i1 hN) = 0 := (mul_eq_zero.mp hgap).resolve_left (by linarith)
    have hu : z (i0 hN) = y / max α β := by simpa [hv] using hc
    exact Set.mem_singleton_iff.mpr (by rw [hshape, hu, hv])
  · rintro rfl
    apply pair_optimal hm hN α β y (y / max α β) 0 hα hβ (by positivity) le_rfl
    · rw [max_eq_left hab.le]
      field_simp
      ring
    · ring

theorem beta_larger {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α β y : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hy : 0 < y) (hab : α < β) :
    lpArgmin (fun _ => 1) (lpVectorA y m) (lpMatrixA α β m N) = {pair hN 0 (y / max α β)} := by
  ext z
  constructor
  · intro hz
    obtain ⟨hshape, heq⟩ := optimal_pair hm hN α β y hα hβ hy z hz
    have hc := optimal_pair_sum hm hN α β y hα hβ hy z hz
    have hprod : β * (z (i0 hN) + z (i1 hN)) = y := by
      rw [hc, max_eq_right hab.le]
      field_simp
    have hgap : (β - α) * z (i0 hN) = 0 := by nlinarith
    have hu : z (i0 hN) = 0 := (mul_eq_zero.mp hgap).resolve_left (by linarith)
    have hv : z (i1 hN) = y / max α β := by simpa [hu] using hc
    exact Set.mem_singleton_iff.mpr (by rw [hshape, hu, hv])
  · rintro rfl
    apply pair_optimal hm hN α β y 0 (y / max α β) hα hβ le_rfl (by positivity)
    · rw [max_eq_right hab.le]
      field_simp
      ring
    · ring

theorem tie {m N : ℕ} (hm : 1 ≤ m) (hN : 3 ≤ N) (α y : ℝ)
    (hα : 0 < α) (hy : 0 < y) :
    lpArgmin (fun _ => 1) (lpVectorA y m) (lpMatrixA α α m N) =
      {z | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = pair hN (y / α * t) (y / α * (1 - t))} := by
  ext z
  constructor
  · intro hz
    obtain ⟨hshape, heq⟩ := optimal_pair hm hN α α y hα hα hy z hz
    have hc := optimal_pair_sum hm hN α α y hα hα hy z hz
    rw [max_self] at hc
    let u := z (i0 hN)
    let v := z (i1 hN)
    have hu : 0 ≤ u := hz.1.2 _
    have hv : 0 ≤ v := hz.1.2 _
    have huv : 0 < u + v := by change 0 < z (i0 hN) + z (i1 hN); rw [hc]; positivity
    refine ⟨u / (u + v), ⟨by positivity, (div_le_one huv).mpr (by linarith)⟩, ?_⟩
    have h0 : y / α * (u / (u + v)) = u := by
      rw [← hc]
      change (u + v) * (u / (u + v)) = u
      field_simp
    have h1 : y / α * (1 - u / (u + v)) = v := by
      rw [← hc]
      change (u + v) * (1 - u / (u + v)) = v
      field_simp
      ring
    rw [h0, h1]
    exact hshape
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    apply pair_optimal hm hN α α y (y / α * t) (y / α * (1 - t)) hα hα
      (by positivity) (mul_nonneg (by positivity) (by linarith))
    · field_simp
      ring
    · rw [max_self]
      ring

end CSmale

theorem solution (m N : ℕ) (hm : 1 ≤ m) (hmN : m < N) (hN : 3 ≤ N)
    (α β y₁ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hy₁ : 0 < y₁) :
    (α > β → lpArgmin (fun _ => 1) (lpVectorA y₁ m) (lpMatrixA α β m N) =
        {fun j : Fin N => if (j : ℕ) = 0 then y₁ / max α β else 0}) ∧
    (β > α → lpArgmin (fun _ => 1) (lpVectorA y₁ m) (lpMatrixA α β m N) =
        {fun j : Fin N => if (j : ℕ) = 1 then y₁ / max α β else 0}) ∧
    (α = β → lpArgmin (fun _ => 1) (lpVectorA y₁ m) (lpMatrixA α β m N) =
        {z | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = fun j : Fin N =>
          if (j : ℕ) = 0 then y₁ / max α β * t
          else if (j : ℕ) = 1 then y₁ / max α β * (1 - t) else 0}) := by
  constructor
  · intro hab
    rw [CSmale.alpha_larger hm hN α β y₁ hα hβ hy₁ hab]
    congr 1
    funext j
    rw [CSmale.pair_apply]
    simp
  constructor
  · intro hab
    rw [CSmale.beta_larger hm hN α β y₁ hα hβ hy₁ hab]
    congr 1
    funext j
    rw [CSmale.pair_apply]
    by_cases hj : (j : ℕ) = 0
    · simp [hj]
    · simp [hj]
  · intro hab
    subst β
    rw [CSmale.tie hm hN α y₁ hα hy₁]
    simp only [max_self]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      funext j
      exact CSmale.pair_apply hN _ _ j
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      funext j
      exact (CSmale.pair_apply hN _ _ j).symm

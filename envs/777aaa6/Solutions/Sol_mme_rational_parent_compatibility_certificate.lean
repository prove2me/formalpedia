-- Prove2me | solution 1 for mme_rational_parent_compatibility_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:32:21.892265+00:00
-- url     : https://prove2.me/submissions/2d6599cd-bf7e-43ba-9e72-3e3a1d5fc6ec

import Theorems.Thm_mme_rational_entropy_difference_certificate
import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_partition_mass_entropy_full_sum

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ

/-- Rational evaluation of the actual parent mixture and regional partition
counts certifies a normalized parent-minus-compatibility entropy bound. -/
theorem solution
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (i : Fin 2) (r : Fin R)
    (kp : (Fin 2 → W) → ℕ)
    (kx : (RecursiveThinSplit.Split half (parent r) ⊕ Fin (half + 1)) → W → ℕ) (b : ℚ) :
    let p : (Fin 2 → W) → ℚ := fun w =>
      (∑ c, (m r c : ℚ) * ((mu ⟨r, c⟩ (w 0) : ℚ) / ∑ v, (mu ⟨r, c⟩ v : ℚ)) *
        ((mu ⟨r, complement (htotal r) c⟩ (w 1) : ℚ) /
          ∑ v, (mu ⟨r, complement (htotal r) c⟩ v : ℚ))) / n r
    let x := fun (t : RecursiveThinSplit.Split half (parent r) ⊕ Fin (half + 1)) w =>
      ((match t with
        | Sum.inl c => if (if i = 0 then (c.val 2).val = 0 else
            (c.val 0).val = 0 ∨ (c.val 1).val = 0) then mu ⟨r, c⟩ w else 0
        | Sum.inr j => ∑ c, if ¬ (if i = 0 then (c.val 2).val = 0 else
            (c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ c.val (yzMode i) = j
            then mu ⟨r, c⟩ w else 0 : ℕ) : ℚ) / n r
    b ≤
      (∑ w, p w * ((kp w : ℚ) * (693147180 / 1000000000) + 1 -
        2 ^ kp w * p w)) -
      ∑ t, (∑ v, x t v) * ∑ v, (x t v / ∑ u, x t u) *
        ((kx t v : ℚ) * (693147181 / 1000000000) - 1 +
          (2 ^ kx t v * (x t v / ∑ u, x t u))⁻¹) →
    (b : ℝ) ≤ entropy (parentMixture htotal n m mu r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
          (fun c w => mu ⟨r, c⟩ w) t w : ℝ) / n r) := by
  intro p x hcert
  have hp (w) : 0 ≤ p w := by
    dsimp [p]
    positivity
  have hx (t) (w) : 0 ≤ x t w := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h := mme_rational_entropy_difference_certificate
    (W := Fin 2 → W)
    (C := RecursiveThinSplit.Split half (parent r) ⊕ Fin (half + 1)) (V := W) p hp x hx kp kx b
  have hh := h hcert
  have hpcast : (fun w => (p w : ℝ)) = parentMixture htotal n m mu r := by
    funext w
    simp only [p, parentMixture, cellFrequency, Rat.cast_div, Rat.cast_sum,
      Rat.cast_mul, Rat.cast_natCast, Nat.cast_sum]
  have hxcast : (∑ t, massEntropy (fun w => (x t w : ℝ))) =
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
          (fun c w => mu ⟨r, c⟩ w) t w : ℝ) / n r) := by
    simp only [x, Rat.cast_div, Rat.cast_natCast]
    have he := mme_partition_mass_entropy_full_sum
      (fun c : RecursiveThinSplit.Split half (parent r) =>
        if i = 0 then (c.val 2).val = 0 else (c.val 0).val = 0 ∨ (c.val 1).val = 0)
      (fun c => c.val (yzMode i)) (fun c w => mu ⟨r, c⟩ w) (n r)
    have hb : (fun c : RecursiveThinSplit.Split half (parent r) => yzBoundary i ⟨r, c⟩) =
        (fun c => if i = 0 then (c.val 2).val = 0 else
          (c.val 0).val = 0 ∨ (c.val 1).val = 0) := by
      funext c
      by_cases hi : i = 0 <;> simp [yzBoundary, hi, yBoundary, zBoundary]
    rw [hb]
    simp only [Fintype.sum_sum_type] at he ⊢
    convert he.symm using 1
    congr 3
    exact Subsingleton.elim _ _
  simpa only [hpcast, hxcast] using hh


#print axioms solution

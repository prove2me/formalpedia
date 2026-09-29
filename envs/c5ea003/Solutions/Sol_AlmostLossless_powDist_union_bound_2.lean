-- Prove2me | solution 2 for AlmostLossless.powDist_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:00:40.302197+00:00
-- url     : https://prove2.me/submissions/6c05b400-5b25-4dde-8692-32cc73de2872

import Definitions.Def_Bridges_MinEntropy
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessBlockDecoding
open AlmostLossless NonArchInfoTheory in
theorem solution {β : Type*} [Fintype β] [DecidableEq β] (μ : FinProbDist β) (b : ℕ)
    (Bs : Fin b → Finset β) :
    setMass (powDist μ b) (Finset.univ.filter (fun x : Fin b → β => ∃ j, x j ∈ Bs j))
      ≤ ∑ j, setMass μ (Bs j) := by
  classical
  have hmarg : ∀ (j : Fin b) (B : Finset β),
      (∑ x : Fin b → β, if x j ∈ B then ∏ i, μ.mass (x i) else 0) = ∑ a ∈ B, μ.mass a := by
    intro j B
    let g : Fin b → β → ℝ := fun i a => if i = j then (if a ∈ B then μ.mass a else 0) else μ.mass a
    have h1 : ∀ x : Fin b → β, (if x j ∈ B then ∏ i, μ.mass (x i) else 0) = ∏ i, g i (x i) := by
      intro x
      by_cases hx : x j ∈ B
      · rw [if_pos hx]
        apply Finset.prod_congr rfl
        intro i _
        by_cases hij : i = j
        · subst hij; simp [g, hx]
        · simp [g, hij]
      · rw [if_neg hx]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [g, hx])
    rw [Finset.sum_congr rfl (fun x _ => h1 x)]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    rw [Finset.prod_eq_single j]
    · simp [g, Finset.sum_ite_mem]
    · intro i _ hij
      simp [g, hij, μ.mass_sum_one]
    · simp
  have hpt : ∀ x : Fin b → β,
      (if ∃ j, x j ∈ Bs j then ∏ i, μ.mass (x i) else 0)
        ≤ ∑ j, (if x j ∈ Bs j then ∏ i, μ.mass (x i) else 0) := by
    intro x
    have hm : 0 ≤ ∏ i, μ.mass (x i) := Finset.prod_nonneg (fun i _ => μ.mass_nonneg (x i))
    split_ifs with hex
    · obtain ⟨j₀, hj₀⟩ := hex
      have := Finset.single_le_sum (f := fun j => if x j ∈ Bs j then ∏ i, μ.mass (x i) else 0)
        (fun j _ => by dsimp only; split_ifs <;> simp [hm]) (Finset.mem_univ j₀)
      simpa [hj₀] using this
    · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hm])
  unfold setMass
  simp only [powDist]
  rw [Finset.sum_filter]
  calc (∑ x : Fin b → β, if ∃ j, x j ∈ Bs j then ∏ i, μ.mass (x i) else 0)
      ≤ ∑ x : Fin b → β, ∑ j, (if x j ∈ Bs j then ∏ i, μ.mass (x i) else 0) :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ j, ∑ x : Fin b → β, (if x j ∈ Bs j then ∏ i, μ.mass (x i) else 0) := Finset.sum_comm
    _ = ∑ j, ∑ a ∈ Bs j, μ.mass a := Finset.sum_congr rfl (fun j _ => hmarg j (Bs j))

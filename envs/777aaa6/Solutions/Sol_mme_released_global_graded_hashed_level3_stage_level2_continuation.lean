-- Prove2me | solution 1 for mme_released_global_graded_hashed_level3_stage_level2_continuation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:27:20.144548+00:00
-- url     : https://prove2.me/submissions/ad54d092-ab26-442b-9133-1fd966159280

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_released_global_graded_hashed_level2_continuation_from_child_windows
import Theorems.Thm_mme_released_square_scale_graded_tolerance_stages
import Theorems.Thm_mme_released_joint_positive_source_inclusion
import Theorems.Thm_mme_released_recursive_stage_region0_rate_margin
import Theorems.Thm_mme_released_recursive_stage_region1_rate_margin
import Theorems.Thm_mme_released_recursive_stage_region2_rate_margin
import Theorems.Thm_mme_released_recursive_stage_region3_rate_margin
import Theorems.Thm_mme_released_recursive_stage_region4_rate_margin
import Theorems.Thm_mme_released_recursive_stage_region5_rate_margin
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

namespace C6Level3

/-- Every permutation of the three modes is realized on a part stage by `rotate`/`swap`,
without changing the number of types or the rate. -/
theorem orient {M lower : ℕ} {S T : Predicate M} (D : LogPartStageG M lower S T)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ D' : LogPartStageG M lower (fun i ↦ S (σ i)) (fun i ↦ T (σ i)),
      D'.types = D.types ∧ D'.rate = D.rate := by
  have key : ∀ σ : Equiv.Perm (Fin 3),
      (∀ i, σ i = i) ∨ (∀ i, σ i = cyclicPerm.symm i) ∨
      (∀ i, σ i = cyclicPerm.symm (cyclicPerm.symm i)) ∨
      (∀ i, σ i = swapFirstTwoPerm.symm i) ∨
      (∀ i, σ i = cyclicPerm.symm (swapFirstTwoPerm.symm i)) ∨
      (∀ i, σ i = cyclicPerm.symm (cyclicPerm.symm (swapFirstTwoPerm.symm i))) := by
    decide
  have hS : ∀ τ : Fin 3 → Fin 3, (∀ i, σ i = τ i) →
      (fun i ↦ S (σ i)) = (fun i ↦ S (τ i)) ∧ (fun i ↦ T (σ i)) = (fun i ↦ T (τ i)) :=
    fun τ h ↦ ⟨funext fun i ↦ by rw [h i], funext fun i ↦ by rw [h i]⟩
  rcases key σ with h | h | h | h | h | h
  · obtain ⟨h1, h2⟩ := hS _ h; rw [h1, h2]; exact ⟨D, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := hS _ h; rw [h1, h2]; exact ⟨D.rotate, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := hS _ h; rw [h1, h2]; exact ⟨D.rotate.rotate, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := hS _ h; rw [h1, h2]; exact ⟨D.swap, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := hS _ h; rw [h1, h2]; exact ⟨D.rotate.swap, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := hS _ h; rw [h1, h2]; exact ⟨D.rotate.rotate.swap, rfl, rfl⟩

theorem blocks_scale (r : Fin 6) (k : ℕ) :
    ReleasedJointInterior.blocks r k = k * ReleasedJointInterior.blocks r 1 := by
  simp only [ReleasedJointInterior.blocks, ReleasedJointInterior.size, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- `2 k^2 B + 1 ≤ (k+1)^(2B+3)` for `k ≥ 1`. -/
theorem poly_bound (k B : ℕ) (hk : 1 ≤ k) :
    2 * (k ^ 2 * B) + 1 ≤ (k + 1) ^ (2 * B + 3) := by
  have h1 : 2 * B + 1 < 2 ^ (2 * B + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * B + 1) ≤ (k + 1) ^ (2 * B + 1) :=
    Nat.pow_le_pow_left (by omega) _
  have h3 : (k + 1) ^ (2 * B + 3) = (k + 1) ^ 2 * (k + 1) ^ (2 * B + 1) := by
    rw [← pow_add]; ring_nf
  rw [h3]
  have h4 : k ^ 2 + 1 ≤ (k + 1) ^ 2 := by nlinarith
  calc 2 * (k ^ 2 * B) + 1 ≤ (k ^ 2 + 1) * (2 * B + 1) := by nlinarith
    _ ≤ (k + 1) ^ 2 * (k + 1) ^ (2 * B + 1) := Nat.mul_le_mul h4 (by omega)

end C6Level3

open C6Level3 in
theorem solution :
    ∀ e : ℝ, 0 < e → e ≤ 1 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2), ∃ a : ∀ o : Fin 6, Reference o (k^2),
          ∃ (size : Fin 6 → ℕ)
            (positions : ((j : Fin 6) × Fin (size j)) ≃ Fin (partSize (k^2) a 1))
            (S T : ∀ j, Predicate (size j))
            (Q : Predicate (partSize (k^2) a 1)),
            (∀ i x, (∀ j, S j i (fun r ↦ x (positions ⟨j, r⟩))) →
              QPos (k^2) a (fun _ ↦ e) i x) ∧
            (∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j, r⟩))) ∧
            ∃ (steps : ∀ j, LogPartStageG (size j) 2 (S j) (T j))
              (next : LogJointRecipeG (partSize (k^2) a 1) 2 Q),
              (∀ j, 1 ≤ (steps j).types ∧ (steps j).types ≤ (k + 1) ^ C) ∧
              (6 * blocks (k^2) : ℝ) * ((7363871 : ℝ)/10000000) ≤ ∑ j, (steps j).rate ∧
              1 ≤ next.inputs ∧
              next.inputs ≤ (k + 1) ^ C ∧
              1 ≤ next.a * next.b * next.c ∧
              (6 * blocks (k^2) : ℝ) * ((5859676 : ℝ)/10000000) ≤ next.logOutputs ∧
              (6 * blocks (k^2) : ℝ) * ((583785872051 : ℝ)/100000000000) ≤
                Real.log ((next.a * next.b * next.c : ℕ) : ℝ) := by
  intro e he0 he1
  -- the six level-3 stage rates, strictly below the proved regional rate margins
  let rates : Fin 6 → ℝ := fun r ↦ (((![122641998732, 122627240242, 122573900880,
    122361213831, 123252768423, 122930062052] : Fin 6 → ℕ) r * 6 * 10 ^ 48 : ℕ) : ℝ)
  have rates_nonneg : ∀ r, 0 ≤ rates r := fun r ↦ Nat.cast_nonneg _
  have rates_below : ∀ r, rates r < RegionRate.regionalRate (RecStage.htotal3 r)
      (RecStage.n3 r) (RecStage.m3 r) (RecStage.mu3 r) := by
    intro r
    fin_cases r
    · exact mme_released_recursive_stage_region0_rate_margin
    · exact mme_released_recursive_stage_region1_rate_margin
    · exact mme_released_recursive_stage_region2_rate_margin
    · exact mme_released_recursive_stage_region3_rate_margin
    · exact mme_released_recursive_stage_region4_rate_margin
    · exact mme_released_recursive_stage_region5_rate_margin
  obtain ⟨δ0, hδ0, hchild⟩ :=
    mme_released_global_graded_hashed_level2_continuation_from_child_windows
  set cap : ℝ := min e (4 * δ0) with hcap_def
  have hcap : 0 < cap := lt_min he0 (by linarith)
  obtain ⟨delta, hdelta, h4delta, hev⟩ :=
    mme_released_square_scale_graded_tolerance_stages rates rates_nonneg rates_below cap hcap
  have hdelta0 : delta ≤ δ0 := by
    have : cap ≤ 4 * δ0 := min_le_right _ _
    linarith
  obtain ⟨C0, hC0⟩ := hchild delta hdelta hdelta0
  obtain ⟨K1, hK1⟩ := Filter.eventually_atTop.1 hev
  -- polynomial degree for the stage type counts
  let B : ℕ := ∑ r, ReleasedJointInterior.blocks r 1
  let X : ℕ := ∑ r : Fin 6, 27 * Fintype.card (Cell 4 88 (RecStage.parent3 r))
  refine ⟨max C0 ((2 * B + 3) * X), fun k0 ↦ ?_⟩
  obtain ⟨k, hk0, a, frame, hnext⟩ := hC0 (max k0 K1)
  refine ⟨k, le_trans (le_max_left _ _) hk0, fun hk ↦ ?_⟩
  obtain ⟨hrep, heps, hsize, -, hstages⟩ := hK1 k (le_trans (le_max_right _ _) hk0)
  obtain ⟨E, hE⟩ := mme_released_joint_positive_source_inclusion (k^2) hk a
  choose st hst using fun r ↦ hstages r (frame r)
  choose st' hst' using fun r ↦ orient (st r) (ReleasedJointInterior.roleEquiv r).symm
  obtain ⟨next, hn1, hn2, hn3, hn4, hn5⟩ := hnext E
  refine ⟨a, _, E, _, _, _, ?_, ?_, st', next, ?_, ?_, hn1,
    le_trans hn2 (Nat.pow_le_pow_right (by omega) (le_max_left _ _)), hn3, hn4, hn5⟩
  · intro i x hx
    exact hE cap hcap (fun _ ↦ e) (fun _ ↦ min_le_left _ _) i x hx
  · intro i y hQ r
    exact hQ r
  · intro r
    rw [(hst' r).1]
    refine ⟨(hst r).2.2, le_trans (hst r).2.1 ?_⟩
    have hk1 : 1 ≤ k := by omega
    have hBr : ReleasedJointInterior.blocks r 1 ≤ B :=
      Finset.single_le_sum (f := fun r ↦ ReleasedJointInterior.blocks r 1)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
    have hXr : 27 * Fintype.card (Cell 4 88 (RecStage.parent3 r)) ≤ X :=
      Finset.single_le_sum (f := fun r : Fin 6 ↦ 27 * Fintype.card (Cell 4 88 (RecStage.parent3 r)))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
    have hbase : 2 * ReleasedJointInterior.blocks r (k ^ 2) + 1 ≤ (k + 1) ^ (2 * B + 3) := by
      rw [blocks_scale r (k ^ 2)]
      calc 2 * (k ^ 2 * ReleasedJointInterior.blocks r 1) + 1 ≤ 2 * (k ^ 2 * B) + 1 := by
            have := Nat.mul_le_mul_left (k ^ 2) hBr
            omega
        _ ≤ _ := poly_bound k B hk1
    calc (2 * ReleasedJointInterior.blocks r (k ^ 2) + 1) ^
          (27 * Fintype.card (Cell 4 88 (RecStage.parent3 r)))
        ≤ ((k + 1) ^ (2 * B + 3)) ^ (27 * Fintype.card (Cell 4 88 (RecStage.parent3 r))) :=
          Nat.pow_le_pow_left hbase _
      _ = (k + 1) ^ ((2 * B + 3) * (27 * Fintype.card (Cell 4 88 (RecStage.parent3 r)))) := by
          rw [← pow_mul]
      _ ≤ (k + 1) ^ ((2 * B + 3) * X) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hXr)
      _ ≤ (k + 1) ^ max C0 ((2 * B + 3) * X) :=
          Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  · have hsum : ∑ r, (st' r).rate = ∑ r, rates r * (k : ℝ) ^ 2 :=
      Finset.sum_congr rfl fun r _ ↦ by rw [(hst' r).2, (hst r).1]
    rw [hsum, ← Finset.sum_mul]
    simp only [rates, blocks, MoreAsymmetryExactSeed.denominator, Fin.sum_univ_six]
    push_cast
    simp
    have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
    nlinarith

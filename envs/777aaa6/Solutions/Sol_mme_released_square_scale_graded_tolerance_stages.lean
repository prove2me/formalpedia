-- Prove2me | solution 1 for mme_released_square_scale_graded_tolerance_stages
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T03:32:15.124044+00:00
-- url     : https://prove2.me/submissions/9be56217-8c52-4a3f-9158-b563a5bb67d4

import Mathlib
import Definitions.Def_mme_released_positive_integer_frame_data
import Definitions.Def_mme_regional_tolerance_window_data
import Theorems.Thm_mme_released_positive_integer_frame
import Theorems.Thm_mme_released_positive_frame_supported_child_words
import Theorems.Thm_mme_regional_square_scale_uniform_window_log_budget
import Theorems.Thm_mme_regional_target_marginals
import Theorems.Thm_mme_graded_regional_tolerance_window_stage

/- This composition uses the public positive-frame, square-scale budget, and
   graded-window interfaces. Every stage keeps the chosen frame's geometry.
   A common radius and threshold are chosen before any varying frame or profile. -/
open BigOperators Filter MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization
  MME.CompleteSplit MME.MoreAsymmetryExactSeed MME.ReleasedPositiveInteger
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MME.SquareScaleGradedStages

/-- The frame already contains the central hypotheses needed by the scalar budget. -/
theorem central_constraints {half ell R M B L : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half}
    {m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ}
    {mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ}
    {length : L * 2 ^ (ell - 1) = M} {minimum : ℕ}
    {grading : Predicate M} {source : ℝ → Predicate M}
    (frame : FrameData (B := B) parent n total m mu length minimum grading source)
    (minimum_pos : 0 < minimum) :
    (∀ r, 0 < n r) ∧ (∀ r, ∑ c, m r c = n r) ∧
      (∀ i cell, ∑ w, mu i cell w =
        m cell.1 cell.2 + m cell.1 (complement (total cell.1) cell.2)) := by
  exact ⟨fun r => minimum_pos.trans_le (frame.parent_size r),
    (mme_regional_target_marginals m 0 frame.reference frame.reference_target).1,
    frame.mass⟩

noncomputable def squareTolerance (a : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (a * ((k + 2 : ℕ) : ℝ) / (k : ℝ) ^ 2)

theorem squareTolerance_pos {a : ℝ} (a_pos : 0 < a) {k : ℕ} (k_pos : 0 < k) :
    0 < squareTolerance a k := by
  have k_real_pos : (0 : ℝ) < k := by exact_mod_cast k_pos
  apply Real.sqrt_pos.2
  positivity

theorem squareTolerance_sq {a : ℝ} (a_nonneg : 0 ≤ a) (k : ℕ) :
    squareTolerance a k ^ 2 = a * ((k + 2 : ℕ) : ℝ) / (k : ℝ) ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- An explicit reciprocal bound gives one threshold for the tolerance schedule. -/
theorem squareTolerance_eventually_small {a cap : ℝ}
    (a_nonneg : 0 ≤ a) (cap_pos : 0 < cap) :
    ∀ᶠ k : ℕ in atTop, squareTolerance a k ≤ cap / 2 := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_ge_atTop (⌈8 * a / cap ^ 2⌉₊)] with k k_large threshold
  have k_two : (2 : ℝ) ≤ k := by exact_mod_cast k_large
  have k_pos : (0 : ℝ) < k := by linarith
  have ceiling_bound : 8 * a / cap ^ 2 ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast threshold)
  have numerator_bound : 8 * a ≤ (k : ℝ) * cap ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos cap_pos)).mp ceiling_bound
  unfold squareTolerance
  rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ cap / 2),
    div_le_iff₀ (sq_pos_of_pos k_pos)]
  push_cast
  have scaled_bound := mul_le_mul_of_nonneg_right numerator_bound k_pos.le
  have linear_bound := mul_le_mul_of_nonneg_left k_two a_nonneg
  nlinarith

/-- The schedule leaves a factor k+2 in the size test, while repair uses k. -/
theorem squareTolerance_size {a : ℝ} (a_nonneg : 0 ≤ a)
    {denom k : ℕ} (denom_pos : 0 < denom) (k_pos : 0 < k) :
    a * k ≤ ((k ^ 2 * denom ^ 2 : ℕ) : ℝ) *
      squareTolerance (a / (denom : ℝ) ^ 2) k ^ 2 := by
  have denom_real_pos : (0 : ℝ) < denom := by exact_mod_cast denom_pos
  have k_real_pos : (0 : ℝ) < k := by exact_mod_cast k_pos
  have identity : ((k ^ 2 * denom ^ 2 : ℕ) : ℝ) *
      squareTolerance (a / (denom : ℝ) ^ 2) k ^ 2 = a * ((k + 2 : ℕ) : ℝ) := by
    rw [squareTolerance_sq (by positivity)]
    push_cast
    field_simp [ne_of_gt denom_real_pos, ne_of_gt k_real_pos]
  rw [identity]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.le_add_right k 2)) a_nonneg

theorem parentTypical_mono {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    {total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half}
    {n : Fin R → ℕ} {m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ}
    {mu : Cell half R parent → W → ℕ} {small large : ℝ} {f : Position n → W}
    (radius_bound : small ≤ large) (typical : parentTypical total n m mu small f) :
    parentTypical total n m mu large f := by
  intro r w
  exact (typical r w).trans_le radius_bound

end MME.SquareScaleGradedStages

open MME.SquareScaleGradedStages

theorem solution
    (rates : Fin 6 → ℝ) (rates_nonneg : ∀ region, 0 ≤ rates region)
    (rates_below : ∀ region, rates region < RegionRate.regionalRate
      (RecStage.htotal3 region) (RecStage.n3 region)
      (RecStage.m3 region) (RecStage.mu3 region))
    (cap : ℝ) (cap_pos : 0 < cap) :
    ∃ delta : ℝ, 0 < delta ∧ 4 * delta ≤ cap ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ repair_gt_one : 1 < k,
        ∃ epsilon_pos : 0 < (Real.sqrt ((8 * 25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2 / (denominator : ℝ) ^ 2) * ((k + 2 : ℕ) : ℝ) / (k : ℝ) ^ 2)),
        ∃ size_test : (8 * k : ℝ) *
          (25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
            ((k ^ 2 * denominator ^ 2 : ℕ) : ℝ) * ((Real.sqrt ((8 * 25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2 / (denominator : ℝ) ^ 2) * ((k + 2 : ℕ) : ℝ) / (k : ℝ) ^ 2))) ^ 2,
          (Real.sqrt ((8 * 25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2 / (denominator : ℝ) ^ 2) * ((k + 2 : ℕ) : ℝ) / (k : ℝ) ^ 2)) + 2 * delta ≤ cap ∧
          ∀ (region : Fin 6) (frame : Frame region (k ^ 2)),
            ∃ stage : LogPartStageG (ReleasedJointInterior.blocks region (k ^ 2) * 4)
                2 (fun i x => ParentGraded (ReleasedJointInterior.parent region) (ReleasedJointInterior.size region (k ^ 2)) i (split (ell := 2) (ReleasedJointInterior.positions region (k ^ 2)) (ReleasedJointInterior.positions_length region (k ^ 2)) x) ∧ ReleasedJointInterior.source region (k ^ 2) cap i x) (childWindow (frame.step (pow_pos (lt_trans Nat.zero_lt_one repair_gt_one) 2) k repair_gt_one (Real.sqrt ((8 * 25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2 / (denominator : ℝ) ^ 2) * ((k + 2 : ℕ) : ℝ) / (k : ℝ) ^ 2)) epsilon_pos size_test) delta),
              stage.rate = rates region * (k : ℝ) ^ 2 ∧
              stage.types ≤ (2 * ReleasedJointInterior.blocks region (k ^ 2) + 1) ^
                (27 * Fintype.card (Cell 4 88 (RecStage.parent3 region))) ∧
              1 ≤ stage.types := by
  classical
  let sizeCoefficient : ℝ := 8 * 25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2
  have word_card : Fintype.card (CompleteWord 2) = 9 := by norm_num [CompleteWord]
  have coefficient_pos : 0 < sizeCoefficient := by
    dsimp [sizeCoefficient]
    rw [word_card]
    norm_num
  have denominator_pos : 0 < denominator := by norm_num [denominator]
  have denominator_real_pos : (0 : ℝ) < denominator := by exact_mod_cast denominator_pos
  let toleranceCoefficient := sizeCoefficient / (denominator : ℝ) ^ 2
  have tolerance_coefficient_pos : 0 < toleranceCoefficient := by
    dsimp [toleranceCoefficient]
    positivity
  let epsilon := squareTolerance toleranceCoefficient
  have central_data (region : Fin 6) :
      (∀ r, 0 < RecStage.n3 region r) ∧
      (∀ r, ∑ c, RecStage.m3 region r c = RecStage.n3 region r) ∧
      (∀ i cell, ∑ w, RecStage.mu3 region i cell w =
        RecStage.m3 region cell.1 cell.2 +
          RecStage.m3 region cell.1 (complement (RecStage.htotal3 region cell.1) cell.2)) := by
    obtain ⟨unitFrame⟩ := mme_released_positive_integer_frame region 1 (by decide)
    have constraints := central_constraints unitFrame (by norm_num [denominator])
    simpa only [one_mul] using constraints
  have region_budgets := fun region : Fin 6 =>
    mme_regional_square_scale_uniform_window_log_budget
      (RecStage.parent3 region) (RecStage.htotal3 region)
      (RecStage.n3 region) (central_data region).1 (by decide)
      (RecStage.m3 region) (central_data region).2.1
      (RecStage.mu3 region) (central_data region).2.2
      toleranceCoefficient tolerance_coefficient_pos (rates region) (rates_below region)
  choose widths width_pos budgets using region_budgets
  let smallest := Finset.univ.inf' (show (Finset.univ : Finset (Fin 6)).Nonempty from
    ⟨0, Finset.mem_univ 0⟩) widths
  have smallest_pos : 0 < smallest := by
    exact (Finset.lt_inf'_iff _).mpr (fun region _ => width_pos region)
  have smallest_le (region : Fin 6) : smallest ≤ widths region :=
    Finset.inf'_le widths (Finset.mem_univ region)
  let delta := min (cap / 4) smallest
  have delta_pos : 0 < delta := lt_min (by positivity) smallest_pos
  have delta_cap : 4 * delta ≤ cap := by
    have bound := min_le_left (cap / 4) smallest
    change delta ≤ cap / 4 at bound
    linarith
  have delta_le (region : Fin 6) : delta ≤ widths region :=
    (min_le_right _ _).trans (smallest_le region)
  have all_budgets := Filter.eventually_all.mpr budgets
  refine ⟨delta, delta_pos, delta_cap, ?_⟩
  filter_upwards [all_budgets,
    squareTolerance_eventually_small tolerance_coefficient_pos.le cap_pos,
    eventually_ge_atTop 2] with k uniform_budget tolerance_small k_large
  have repair_gt_one : 1 < k := by omega
  have k_pos : 0 < k := lt_trans Nat.zero_lt_one repair_gt_one
  have epsilon_pos : 0 < epsilon k := squareTolerance_pos tolerance_coefficient_pos k_pos
  have size_test : (8 * k : ℝ) *
      (25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
        ((k ^ 2 * denominator ^ 2 : ℕ) : ℝ) * (epsilon k) ^ 2 := by
    have bound := squareTolerance_size coefficient_pos.le denominator_pos k_pos
    change sizeCoefficient * (k : ℝ) ≤ _ at bound
    convert bound using 1
    dsimp [sizeCoefficient]
    ring
  have radius_bound : epsilon k + 2 * delta ≤ cap := by
    change epsilon k ≤ cap / 2 at tolerance_small
    linarith
  refine ⟨repair_gt_one, epsilon_pos, size_test, radius_bound, ?_⟩
  intro region frame
  let centralStep := frame.step (pow_pos k_pos 2) k repair_gt_one
    (epsilon k) epsilon_pos size_test
  let commonSource : Predicate (ReleasedJointInterior.blocks region (k ^ 2) * 4) :=
    fun i x =>
      ParentGraded (ReleasedJointInterior.parent region)
        (ReleasedJointInterior.size region (k ^ 2)) i
        (split (ell := 2) (ReleasedJointInterior.positions region (k ^ 2))
          (ReleasedJointInterior.positions_length region (k ^ 2)) x) ∧
      ReleasedJointInterior.source region (k ^ 2) cap i x
  have source_inside : ∀ i x,
      ParentGraded centralStep.parent centralStep.n i
        (split centralStep.positions centralStep.length x) →
      parentWindow centralStep (epsilon k + 2 * delta) i x → commonSource i x := by
    intro i x parent_graded in_band
    refine ⟨(frame.parent_graded i x).mp parent_graded, ?_⟩
    apply (frame.typical cap cap_pos i x).mp
    exact parentTypical_mono radius_bound in_band
  have scalar_budget : ∀ profile : WindowProfile centralStep,
      WindowAdmissible centralStep profile →
      (∀ i, WindowClose centralStep delta i (profile i)) →
        rates region * (k : ℝ) ^ 2 ≤ windowLogBudget centralStep profile (epsilon k) := by
    intro profile admissible close
    have profile_close : ∀ i cell w,
        |cellFrequency (profile i) cell w -
          cellFrequency (fun cell w => k ^ 2 * RecStage.mu3 region i cell w) cell w| ≤
            widths region := by
      intro i cell w
      exact (close i cell w).trans (delta_le region)
    exact uniform_budget region profile admissible.1 profile_close frame.reference
  have scaled_rate_nonneg : 0 ≤ rates region * (k : ℝ) ^ 2 :=
    mul_nonneg (rates_nonneg region) (sq_nonneg _)
  obtain ⟨stage, rate_eq, type_bound, nonempty_types⟩ :=
    mme_graded_regional_tolerance_window_stage centralStep delta (epsilon k)
      (rates region * (k : ℝ) ^ 2) delta_pos.le epsilon_pos scaled_rate_nonneg
      size_test source_inside scalar_budget
  have stage_nonempty : 1 ≤ stage.types := by
    apply nonempty_types
    obtain ⟨words, words_supported, exact_profiles⟩ :=
      mme_released_positive_frame_supported_child_words region (k ^ 2) frame
    refine ⟨words, words_supported, ?_⟩
    intro i
    refine ⟨(exact_profiles i).1, ?_⟩
    have exact_histogram :
        count (fullCell centralStep.total centralStep.reference)
          (split centralStep.positions centralStep.length (words i)) = centralStep.mu i := by
      funext cell word
      exact (exact_profiles i).2 cell word
    unfold WindowClose
    rw [exact_histogram]
    intro cell word
    simpa only [sub_self, abs_zero] using delta_pos.le
  refine ⟨stage, rate_eq, ?_, stage_nonempty⟩
  have position_card : Fintype.card (Position centralStep.n) =
      2 * ReleasedJointInterior.blocks region (k ^ 2) := by
    have equality := Fintype.card_congr frame.positions
    simpa only [Fintype.card_fin, Nat.mul_comm] using equality.symm
  have degree_eq : 3 * Fintype.card (Cell 4 88 (RecStage.parent3 region)) * 9 =
      27 * Fintype.card (Cell 4 88 (RecStage.parent3 region)) := by ring
  rw [position_card, word_card] at type_bound
  change stage.types ≤ (2 * ReleasedJointInterior.blocks region (k ^ 2) + 1) ^
    (3 * Fintype.card (Cell 4 88 (RecStage.parent3 region)) * 9) at type_bound
  rw [degree_eq] at type_bound
  exact type_bound

#print axioms solution

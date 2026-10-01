-- Prove2me | solution 1 for mme_elementary_supported_stage_exact_volume
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T08:15:32.073494+00:00
-- url     : https://prove2.me/submissions/200eed53-79fb-4737-b9c4-6310874aa850

import Theorems.Thm_mme_graded_integer_step_low_level_log_recipe
import Theorems.Thm_mme_low_level_boundary_profile_dimension

open BigOperators MME MME.RecursiveYZ MME.ProfiledCW MME.CompleteSplit
  MME.RegionRealization MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000

private theorem profile_one_count {L : ℕ} (B : Boundary.Profile 1 L) :
    B.count (fun _ ↦ 1) = if B.index = 1 then L else 0 := by
  classical
  have hg : grade (fun _ ↦ (1 : Fin 3) : CompleteWord 1) = 1 := by
    simp [CWCells.grade]
  by_cases hi : B.index = 1
  · have hz (w : CompleteWord 1) (hw : w ≠ (fun _ ↦ 1)) : B.count w = 0 := by
      by_contra hc
      have h := B.supported w hc
      rw [hi] at h
      have h0 : w 0 = 1 := Fin.ext (by simpa [CWCells.grade] using h)
      apply hw
      funext r
      have hr : r = 0 := by fin_cases r; rfl
      simpa only [hr] using h0
    have hc := Finset.sum_eq_single (s := Finset.univ) (fun _ ↦ (1 : Fin 3) : CompleteWord 1)
      (fun w _ hw ↦ hz w hw) (by simp)
    simpa only [if_pos hi] using hc.symm.trans B.total
  · have hc : B.count (fun _ ↦ 1) = 0 := by
      by_contra hn
      exact hi ((B.supported _ hn).symm.trans hg)
    simp only [if_neg hi, hc]

private theorem profile_volume_square {L : ℕ} (B : Boundary.Profile 1 L) (z : Fin 3) :
    (B.a z * B.b z * B.c z) ^ 2 =
      5 ^ (∑ i : Fin 3, B.mu z i (fun _ ↦ 1)) := by
  classical
  have hf : Boundary.flipLabel (fun _ ↦ (1 : Fin 3) : CompleteWord 1) =
      (fun _ ↦ 1) := by funext r; rfl
  have hn : (fun _ ↦ (1 : Fin 3) : CompleteWord 1) ≠ (fun _ ↦ 0) := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hz : z = 0 ∨ z = 1 ∨ z = 2 := by omega
  have hmu : (∑ i : Fin 3, B.mu z i (fun _ ↦ 1)) =
      2 * (if B.index = 1 then L else 0) := by
    rw [Fin.sum_univ_three]
    rcases hz with rfl | rfl | rfl
    · change (if (fun _ ↦ (1 : Fin 3) : CompleteWord 1) = (fun _ ↦ 0) then L else 0) +
        B.count (fun _ ↦ 1) + B.count (Boundary.flipLabel (fun _ ↦ 1)) = _
      rw [if_neg hn, hf, profile_one_count]
      omega
    · change B.count (Boundary.flipLabel (fun _ ↦ 1)) +
        (if (fun _ ↦ (1 : Fin 3) : CompleteWord 1) = (fun _ ↦ 0) then L else 0) +
        B.count (fun _ ↦ 1) = _
      rw [if_neg hn, hf, profile_one_count]
      omega
    · change B.count (fun _ ↦ 1) + B.count (Boundary.flipLabel (fun _ ↦ 1)) +
        (if (fun _ ↦ (1 : Fin 3) : CompleteWord 1) = (fun _ ↦ 0) then L else 0) = _
      rw [if_neg hn, hf, profile_one_count]
      omega
  have habc : B.a z * B.b z * B.c z = B.dim := by
    rcases hz with rfl | rfl | rfl
    all_goals simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]
  rw [hmu, habc, mme_low_level_boundary_profile_dimension B (by decide)]
  split_ifs <;> simp [pow_mul, mul_comm]

private theorem profile_dims_positive {L : ℕ} (B : Boundary.Profile 1 L) (z : Fin 3) :
    1 ≤ B.a z ∧ 1 ≤ B.b z ∧ 1 ≤ B.c z := by
  have hd : 1 ≤ B.dim := by
    rw [mme_low_level_boundary_profile_dimension B (by decide)]
    split_ifs
    · exact Nat.one_le_pow L 5 (by decide)
    · rfl
  simp only [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]
  split_ifs <;> omega

private theorem histogram_one_count {P C : Type} [Fintype P] [Fintype C]
    {L M : ℕ} (cell : P → C) (positions : Fin L ≃ P)
    (length : L * 2 ^ (1 - 1) = M) (x : FineWord M) :
    (∑ c, count cell (split positions length x) c (fun _ ↦ 1)) =
      ∑ r, if x r = 1 then 1 else 0 := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  trans ∑ p, if split positions length x p = (fun _ ↦ 1) then 1 else 0
  · apply Finset.sum_congr rfl
    intro p _
    by_cases h : split positions length x p = (fun _ ↦ 1)
    · simp only [h, and_true, if_true]
      simp [eq_comm]
    · simp only [h, and_false, if_false, Finset.sum_const_zero]
  letI : Unique (Fin (2 ^ (1 - 1))) := by change Unique (Fin 1); infer_instance
  have hdefault : (default : Fin (2 ^ (1 - 1))) = 0 := by
    change (default : Fin 1) = 0
    exact Subsingleton.elim _ _
  let e : P ≃ Fin M := positions.symm.trans
    ((Equiv.prodUnique (Fin L) (Fin (2 ^ (1 - 1)))).symm.trans
      (finProdFinEquiv.trans (finCongr length)))
  apply Fintype.sum_equiv e
  intro p
  have hw : split positions length x p = (fun _ ↦ 1) ↔ x (e p) = 1 := by
    constructor
    · intro h
      simpa [e, split, Equiv.prodUnique_symm_apply, hdefault] using congrFun h 0
    · intro h
      funext r
      have hr : r = 0 := by fin_cases r; rfl
      simpa [hr, e, split, Equiv.prodUnique_symm_apply, hdefault] using h
  simp only [hw]

private theorem integer_terminal_volume {M upper : ℕ} {S : Predicate M}
    (D : IntegerStepG 1 M S) (hupper : 1 < upper)
    (x : Fin 3 → FineWord M) (hx : ∀ i, D.step.output i (x i))
    (rate : ℝ) (hr : 0 ≤ rate) (hb : rate ≤ D.step.certifiedLogCopies) :
    ∃ E : LogJointRecipeG M upper S,
      E.inputs = 1 ∧ E.logOutputs = rate ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      (E.a * E.b * E.c) ^ 2 =
        5 ^ (∑ i : Fin 3, ∑ r : Fin M, if x i r = 1 then 1 else 0) := by
  classical
  let part := Partition.canonical (fullCell D.step.total D.step.reference)
  obtain ⟨z, profiles, _, hmu, E, hinput, hrate, hdims⟩ :=
    mme_graded_integer_step_low_level_log_recipe D (by decide) hupper part rate hr hb
  have ha : 1 ≤ E.a := by
    change 1 ≤ E.dims.1
    rw [hdims]
    dsimp only [Prod.fst]
    exact Finset.one_le_prod' (fun j _ ↦ (profile_dims_positive (profiles j) (z j)).1)
  have hb' : 1 ≤ E.b := by
    change 1 ≤ E.dims.2.1
    rw [hdims]
    dsimp only [Prod.fst, Prod.snd]
    exact Finset.one_le_prod' (fun j _ ↦ (profile_dims_positive (profiles j) (z j)).2.1)
  have hc : 1 ≤ E.c := by
    change 1 ≤ E.dims.2.2
    rw [hdims]
    dsimp only [Prod.snd]
    exact Finset.one_le_prod' (fun j _ ↦ (profile_dims_positive (profiles j) (z j)).2.2)
  refine ⟨E, hinput, hrate, ha, hb', hc, ?_⟩
  have hv : E.a * E.b * E.c =
      ∏ j, (profiles j).a (z j) * (profiles j).b (z j) * (profiles j).c (z j) := by
    change E.dims.1 * E.dims.2.1 * E.dims.2.2 = _
    rw [hdims]
    dsimp only [Prod.fst, Prod.snd]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have he : (∑ j, ∑ i : Fin 3, (profiles j).mu (z j) i (fun _ ↦ 1)) =
      ∑ i : Fin 3, ∑ r : Fin M, if x i r = 1 then 1 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ∑ j, D.step.mu i (part.cells j) (fun _ ↦ 1) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hmu j i]
      _ = ∑ c, D.step.mu i c (fun _ ↦ 1) :=
        part.cells.sum_comp (fun c ↦ D.step.mu i c (fun _ ↦ 1))
      _ = ∑ c, count (fullCell D.step.total D.step.reference)
          (split D.step.positions D.step.length (x i)) c (fun _ ↦ 1) := by
        apply Finset.sum_congr rfl
        intro c _
        exact ((hx i).2 c _).symm
      _ = _ := histogram_one_count _ _ _ _
  rw [hv, ← Finset.prod_pow]
  simp_rw [profile_volume_square]
  rw [Finset.prod_pow_eq_pow_sum, he]

/-- The supported type selected by the stage cover has its elementary matrix
volume determined by the grade-one counts of the target triple. -/
theorem solution
    {M upper : ℕ} {S T : Predicate M}
    (D : LogPartStageG M 1 S T) (hupper : 1 < upper)
    (x : Fin 3 → FineWord M) (hs : supported x) (ht : ∀ i, T i (x i)) :
    ∃ E : LogJointRecipeG M upper S,
      E.inputs = 1 ∧ E.logOutputs = D.rate ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      (E.a * E.b * E.c) ^ 2 =
        5 ^ (∑ i : Fin 3, ∑ r : Fin M, if x i r = 1 then 1 else 0) := by
  induction D generalizing x with
  | step types rate hr steps budget inside cover =>
    obtain ⟨j, hj, _⟩ := cover x hs ht
    exact integer_terminal_volume (steps j) hupper x hj rate hr (budget j)
  | rotate D ih =>
    have hs' : supported (fun i ↦ x (cyclicPerm i)) := by
      intro r
      have := hs r
      change (x 1 r).val + (x 2 r).val + (x 0 r).val = 2
      omega
    obtain ⟨E, hE, hr, ha, hb, hc, hv⟩ := ih (fun i ↦ x (cyclicPerm i)) hs'
      (fun i ↦ by simpa only [Equiv.symm_apply_apply] using ht (cyclicPerm i))
    refine ⟨.rotate E, hE, hr, hc, ha, hb, ?_⟩
    change (E.c * E.a * E.b) ^ 2 = _
    rw [show E.c * E.a * E.b = E.a * E.b * E.c by ring, hv]
    congr 1
    exact Fintype.sum_equiv cyclicPerm _ _ (fun _ ↦ rfl)
  | swap D ih =>
    have hs' : supported (fun i ↦ x (swapFirstTwoPerm i)) := by
      intro r
      have := hs r
      change (x 1 r).val + (x 0 r).val + (x 2 r).val = 2
      omega
    obtain ⟨E, hE, hr, ha, hb, hc, hv⟩ := ih (fun i ↦ x (swapFirstTwoPerm i)) hs'
      (fun i ↦ by simpa only [Equiv.symm_apply_apply] using ht (swapFirstTwoPerm i))
    refine ⟨.swap E, hE, hr, hc, hb, ha, ?_⟩
    change (E.c * E.b * E.a) ^ 2 = _
    rw [show E.c * E.b * E.a = E.a * E.b * E.c by ring, hv]
    congr 1
    exact Fintype.sum_equiv swapFirstTwoPerm _ _ (fun _ ↦ rfl)

#print axioms solution

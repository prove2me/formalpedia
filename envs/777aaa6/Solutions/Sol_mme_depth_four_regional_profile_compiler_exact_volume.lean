-- Prove2me | solution 1 for mme_depth_four_regional_profile_compiler_exact_volume
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T08:18:04.360359+00:00
-- url     : https://prove2.me/submissions/d78882c6-f648-43b5-ac8a-a72096268fd9

import Definitions.Def_mme_regional_profile_layer_compiler_data
import Theorems.Thm_mme_regional_fixed_parent_window_square_stage
import Theorems.Thm_mme_regional_supported_histograms_of_joint_certificate
import Theorems.Thm_mme_graded_integer_step_low_level_log_recipe
import Theorems.Thm_mme_low_level_boundary_profile_dimension

open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfileCompiler
  MME.ProfiledCW MME.CompleteSplit MME.RecursiveYZ.CWCells
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
private theorem supported_terminal_volume
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


private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

private theorem histogram_mass {P C W : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (f : P → W) (c : C) :
    ∑ w, count cell f c w = Fintype.card {p : P // cell p = c} := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : cell p = c <;> simp [hp]


private theorem stage_positive {M lower : ℕ}
    {S T : ProfiledCW.Predicate M} (D : LogPartStageG M lower S T) :
    ∀ x : Fin 3 → ProfiledCW.FineWord M,
      ProfiledCW.supported x → (∀ i, T i (x i)) → 1 ≤ D.types := by
  induction D with
  | step types rate hr steps budget inside cover =>
    intro x hs ht
    obtain ⟨j, _, _⟩ := cover x hs ht
    have := j.isLt
    dsimp only [LogPartStageG.types]
    omega
  | rotate D ih =>
    intro x hs ht
    apply ih (fun i ↦ x (cyclicPerm i))
    · intro r
      have := hs r
      change (x 1 r).val + (x 2 r).val + (x 0 r).val = 2
      omega
    · intro i
      simpa only [Equiv.symm_apply_apply] using ht (cyclicPerm i)
  | swap D ih =>
    intro x hs ht
    apply ih (fun i ↦ x (swapFirstTwoPerm i))
    · intro r
      have := hs r
      change (x 1 r).val + (x 0 r).val + (x 2 r).val = 2
      omega
    · intro i
      simpa only [Equiv.symm_apply_apply] using ht (swapFirstTwoPerm i)

private theorem packet_histogram_mass {ell : ℕ} (p : Packet ell) (k : ℕ)
    (x : FineWord (p.size k)) (c : p.Cells) :
    ∑ w, p.histogram k x c w = k ^ 2 * p.mass c := by
  classical
  have ha := (Finset.mem_filter.mp (p.address_valid k)).2
  have hf := full_cell_fiber p.total (p.address k) c.1 c.2
  rw [ha, ha] at hf
  change ∑ w, count _ _ c w = _
  rw [histogram_mass]
  simpa only [Fintype.card_eq_nat_card, Packet.mass, mul_add] using hf

/-- The joint table ensures the stage's cover has an inhabited exact type. -/
private theorem packet_exact_supported {ell : ℕ} (p : Packet ell) (k : ℕ) (hk : 0 < k)
    (delta : ℝ) (hd : 0 ≤ delta) :
    ∃ x : Fin 3 → FineWord (p.size k), supported x ∧ (∀ i, p.target delta k i (x i)) ∧
      ∀ i c w, p.histogram k (x i) c w = k ^ 2 * p.mu i c w := by
  classical
  have hk2 : 0 < k ^ 2 := pow_pos hk _
  have ha := (Finset.mem_filter.mp (p.address_valid k)).2
  obtain ⟨x, hs, hx⟩ := mme_regional_supported_histograms_of_joint_certificate
    p.parent p.total (fun r ↦ k ^ 2 * p.n r) (p.address k)
    (MME.DWZProfiledRegional.positionsAt p.n (k ^ 2)) rfl
    (fun c z ↦ k ^ 2 * p.joint c z) (fun i c w ↦ k ^ 2 * p.mu i c w)
    (by
      intro c
      rw [← Finset.mul_sum, p.joint_mass]
      have hf := full_cell_fiber p.total (p.address k) c.1 c.2
      rw [ha, ha] at hf
      simpa only [Fintype.card_eq_nat_card, mul_add] using hf.symm)
    (by intro c z hz; exact p.joint_support c z (by nlinarith))
    (by intro c z hz; exact p.joint_grade c z (by nlinarith))
    (by
      intro i c w
      rw [← Finset.mul_sum]
      congr 1
      exact p.joint_marginal i c w)
  refine ⟨x, hs, ?_, ?_⟩
  · intro i
    refine ⟨(hx i).1, ?_, ?_⟩
    · intro c
      apply Finset.sum_congr rfl
      intro w hw
      exact (hx i).2 c w
    · intro c w
      dsimp only [Packet.histogram, Packet.words]
      change |((_ : ℕ) : ℝ) - ((k ^ 2 * p.mu i c w : ℕ) : ℝ)| ≤ _
      rw [(hx i).2 c w, sub_self, abs_zero]
      exact mul_nonneg hd (Nat.cast_nonneg _)
  · exact fun i c w ↦ (hx i).2 c w

private theorem packet_stages {ell : ℕ} (p : Packet ell) (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ D : LogPartStageG (p.size k) ell (p.source eps k) (p.target delta k),
        1 ≤ D.types ∧ D.types ≤ (k + 1) ^ p.degree ∧ D.rate = p.rate * k ^ 2 := by
  classical
  obtain ⟨delta, hd, k0, h⟩ := mme_regional_fixed_parent_window_square_stage
    p.parent p.total p.n p.n_pos p.regions_pos p.m p.m_mass p.mu p.mu_mass
    p.rate eps p.rate_nonneg p.rate_strict heps p.center (by intros; rfl)
  refine ⟨delta, hd, k0, ?_⟩
  intro k hk
  obtain ⟨hkpos, hh⟩ := h k hk
  obtain ⟨D, ht, hr⟩ := hh (p.address k) (p.address_valid k)
  obtain ⟨x, hs, hx, _⟩ := packet_exact_supported p k hkpos delta hd.le
  exact ⟨D, stage_positive D x hs hx, ht, hr⟩

private theorem layer_stages {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : Fin L.parts → ℝ, (∀ j, 0 < delta j) ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ D : ∀ j, LogPartStageG ((L.packet j).size k) ell
        ((L.packet j).source eps k) ((L.packet j).target (delta j) k),
        (∀ j, 1 ≤ (D j).types ∧ (D j).types ≤ (k + 1) ^ (L.packet j).degree) ∧
        (∀ j, (D j).rate = (L.packet j).rate * k ^ 2) := by
  classical
  choose delta hd k0 h using fun j ↦ packet_stages (L.packet j) eps heps
  refine ⟨delta, hd, Finset.univ.sup k0, ?_⟩
  intro k hk
  have h' : ∀ j, ∃ D : LogPartStageG ((L.packet j).size k) ell
      ((L.packet j).source eps k) ((L.packet j).target (delta j) k),
      1 ≤ D.types ∧ D.types ≤ (k + 1) ^ (L.packet j).degree ∧
      D.rate = (L.packet j).rate * k ^ 2 :=
    fun j ↦ h j k ((Finset.le_sup (f := k0) (Finset.mem_univ j)).trans hk)
  choose D hD using h'
  exact ⟨D, fun j ↦ ⟨(hD j).1, (hD j).2.1⟩, fun j ↦ (hD j).2.2⟩

/-- Positive radii have a common positive lower bound, including the empty family. -/
private theorem common_radius {p : ℕ} (delta : Fin p → ℝ) (hd : ∀ j, 0 < delta j) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ j, eps ≤ delta j := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image delta)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.inf' hs id, (Finset.lt_inf'_iff hs).mpr ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simpa only [hx] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact hd j
  · intro j
    exact Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ j, rfl⟩))

/-- Exact finite count and center routing gives the required window inclusion. -/
private theorem bridge_target {upper lower : ℕ} {N : ℕ → ℕ}
    {A : Layer upper N} {B : Layer lower N} (H : Bridge A B)
    (eps : ℝ) (he : 0 ≤ eps) (delta : Fin A.parts → ℝ)
    (hed : ∀ j, eps ≤ delta j) (k : ℕ) :
    ∀ i x, B.source eps k i x →
      ∀ j, (A.packet j).target (delta j) k i (A.piece k x j) := by
  classical
  intro i x hx j
  refine ⟨H.grade_identity k i x (fun j ↦ (hx j).1) j, ?_, ?_⟩
  · intro c
    rw [packet_histogram_mass, ← Finset.mul_sum, (A.packet j).mu_mass]
    rfl
  · intro c w
    have ho : ∀ o : B.Observations, |B.observe k x o - B.center i o| ≤ eps :=
      fun o ↦ ((hx o.1).2 o.2.1 o.2.2).le
    have hb : |∑ o, H.weight j c w o * (B.observe k x o - B.center i o)| ≤ eps := by
      calc
        _ ≤ ∑ o, |H.weight j c w o * (B.observe k x o - B.center i o)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ o, H.weight j c w o * |B.observe k x o - B.center i o| := by
          apply Finset.sum_congr rfl
          intro o ho'
          rw [abs_mul, abs_of_nonneg (H.weight_nonneg j c w o)]
        _ ≤ ∑ o, H.weight j c w o * eps := Finset.sum_le_sum
          (fun o _ ↦ mul_le_mul_of_nonneg_left (ho o) (H.weight_nonneg j c w o))
        _ = (∑ o, H.weight j c w o) * eps := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * eps := mul_le_mul_of_nonneg_right (H.weight_sum j c w) he
        _ = eps := one_mul _
    have hid : ((A.packet j).histogram k (A.piece k x j) c w : ℝ) -
        ((k ^ 2 * (A.packet j).mu i c w : ℕ) : ℝ) =
        ((k ^ 2 * (A.packet j).mass c : ℕ) : ℝ) *
          ∑ o, H.weight j c w o * (B.observe k x o - B.center i o) := by
      rw [H.count_identity k i x j c w, Nat.cast_mul, Nat.cast_mul,
        H.center_identity i j c w]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hm : (∑ z, k ^ 2 * (A.packet j).mu i c z : ℕ) =
        k ^ 2 * (A.packet j).mass c := by
      rw [← Finset.mul_sum, (A.packet j).mu_mass]
      rfl
    rw [hm]
    exact (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)).trans
      (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (hed j) (Nat.cast_nonneg (k ^ 2 * (A.packet j).mass c)))



private theorem terminal_layer {N : ℕ → ℕ} (L : Layer 1 N) (eps : ℝ) (he : 0 < eps) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ E : LogJointRecipeG (N k) 2 (L.source eps k),
      E.inputs = 1 ∧ E.logOutputs = L.rate * k ^ 2 ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      (E.a * E.b * E.c) ^ 2 =
        5 ^ (k ^ 2 * ∑ j, ∑ i : Fin 3, ∑ c, (L.packet j).mu i c (fun _ ↦ 1)) := by
  classical
  obtain ⟨delta, hd, k0, h⟩ := layer_stages L eps he
  refine ⟨max 1 k0, ?_⟩
  intro k hk
  have hkpos : 0 < k := by have := (le_max_left 1 k0).trans hk; omega
  obtain ⟨D, hp, hr⟩ := h k ((le_max_right 1 k0).trans hk)
  have hparts : ∀ j, ∃ E : LogJointRecipeG ((L.packet j).size k) 2
      ((L.packet j).source eps k), E.inputs = 1 ∧ E.logOutputs = (D j).rate ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      (E.a * E.b * E.c) ^ 2 =
        5 ^ (k ^ 2 * ∑ i : Fin 3, ∑ c, (L.packet j).mu i c (fun _ ↦ 1)) := by
    intro j
    obtain ⟨x, hs, ht, hx⟩ := packet_exact_supported (L.packet j) k hkpos (delta j) (hd j).le
    obtain ⟨E, hi, hr, ha, hb, hc, hv⟩ :=
      supported_terminal_volume (D j) (by decide : 1 < 2) x hs ht
    refine ⟨E, hi, hr, ha, hb, hc, ?_⟩
    rw [hv]
    congr 1
    calc
      _ = ∑ i : Fin 3, ∑ c, (L.packet j).histogram k (x i) c (fun _ ↦ 1) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (histogram_one_count (fullCell (L.packet j).total ((L.packet j).address k))
          (MME.DWZProfiledRegional.positionsAt (L.packet j).n (k ^ 2)) rfl (x i)).symm
      _ = ∑ i : Fin 3, ∑ c, k ^ 2 * (L.packet j).mu i c (fun _ ↦ 1) := by
        simp_rw [hx]
      _ = _ := by simp only [Finset.mul_sum]
  choose E hE using hparts
  let R : LogJointRecipeG (N k) 2 (L.source eps k) :=
    .partition (fun j ↦ (L.packet j).size k) (L.positions k)
      (fun j ↦ (L.packet j).source eps k) (by intro i x h; exact h) E
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (∏ j, (E j).inputs) = 1
    simp only [fun j ↦ (hE j).1, Finset.prod_const_one]
  · change (∑ j, (E j).logOutputs) = L.rate * k ^ 2
    simp only [fun j ↦ (hE j).2.1, hr]
    exact (Finset.sum_mul _ _ _).symm
  · change 1 ≤ ∏ j, (E j).a
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.1)
  · change 1 ≤ ∏ j, (E j).b
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.1)
  · change 1 ≤ ∏ j, (E j).c
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.2.1)
  · change ((∏ j, (E j).a) * (∏ j, (E j).b) * (∏ j, (E j).c)) ^ 2 = _
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    simp_rw [fun j ↦ (hE j).2.2.2.2.2]
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]

private theorem extend_layer {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N)
    (eps : ℝ) (delta : Fin L.parts → ℝ) (k : ℕ)
    (D : ∀ j, LogPartStageG ((L.packet j).size k) ell
      ((L.packet j).source eps k) ((L.packet j).target (delta j) k))
    (hp : ∀ j, 1 ≤ (D j).types ∧ (D j).types ≤ (k + 1) ^ (L.packet j).degree)
    (hr : ∀ j, (D j).rate = (L.packet j).rate * k ^ 2)
    (Q : Predicate (N k))
    (ht : ∀ i x, Q i x → ∀ j, (L.packet j).target (delta j) k i (L.piece k x j))
    (next : LogJointRecipeG (N k) ell Q) (degree : ℕ)
    (hn : 1 ≤ next.inputs ∧ next.inputs ≤ (k + 1) ^ degree) :
    ∃ E : LogJointRecipeG (N k) (ell + 1) (L.source eps k),
      1 ≤ E.inputs ∧ E.inputs ≤ (k + 1) ^ (L.degree + degree) ∧
      E.logOutputs = L.rate * k ^ 2 + next.logOutputs ∧
      E.a = next.a ∧ E.b = next.b ∧ E.c = next.c := by
  classical
  let E : LogJointRecipeG (N k) (ell + 1) (L.source eps k) :=
    .stage (Nat.lt_succ_self ell) (fun j ↦ (L.packet j).size k) (L.positions k)
      (fun j ↦ (L.packet j).source eps k) (fun j ↦ (L.packet j).target (delta j) k)
      (by intro i x h; exact h) D ht next
  refine ⟨E, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · change 1 ≤ (∏ j, (D j).types) * next.inputs
    exact one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' (fun j _ ↦ (hp j).1)) hn.1
  · change (∏ j, (D j).types) * next.inputs ≤ _
    calc
      _ ≤ (∏ j, (k + 1) ^ (L.packet j).degree) * (k + 1) ^ degree :=
        Nat.mul_le_mul (Finset.prod_le_prod' (fun j _ ↦ (hp j).2)) hn.2
      _ = (k + 1) ^ (L.degree + degree) := by
        rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
        rfl
  · change (∑ j, (D j).rate) + next.logOutputs = _
    simp only [hr]
    rw [← Finset.sum_mul]
    rfl

/-- Three feasible integer profile layers and finite routing identities compile
to actual depth-four recipes at every sufficiently large square scale. -/
theorem solution
    {N : ℕ → ℕ} (L3 : Layer 3 N) (L2 : Layer 2 N) (L1 : Layer 1 N)
    (H32 : Bridge L3 L2) (H21 : Bridge L2 L1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ E : LogJointRecipeG (N k) 4 (L3.source eps k),
        1 ≤ E.inputs ∧ E.inputs ≤ (k + 1) ^ (L3.degree + L2.degree) ∧
        E.logOutputs = (L3.rate + L2.rate + L1.rate) * k ^ 2 ∧
        1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
        Real.log ((E.a * E.b * E.c : ℕ) : ℝ) =
          (k ^ 2 : ℝ) *
            (((∑ j, ∑ i : Fin 3, ∑ c, (L1.packet j).mu i c (fun _ ↦ 1) : ℕ) : ℝ) / 2 *
              Real.log 5) := by
  classical
  obtain ⟨d3, hd3, k3, hs3⟩ := layer_stages L3 eps heps
  obtain ⟨e2, he2, he23⟩ := common_radius d3 hd3
  obtain ⟨d2, hd2, k2, hs2⟩ := layer_stages L2 e2 he2
  obtain ⟨e1, he1, he12⟩ := common_radius d2 hd2
  obtain ⟨k1, ht1⟩ := terminal_layer L1 e1 he1
  refine ⟨max k3 (max k2 k1), ?_⟩
  intro k hk
  obtain ⟨D3, hp3, hr3⟩ := hs3 k ((le_max_left _ _).trans hk)
  obtain ⟨D2, hp2, hr2⟩ := hs2 k ((le_max_left k2 k1).trans ((le_max_right _ _).trans hk))
  obtain ⟨E1, hinput1, hrate1, ha1, hb1, hc1, hv1⟩ :=
    ht1 k ((le_max_right k2 k1).trans ((le_max_right _ _).trans hk))
  obtain ⟨E2, hpE2, hbE2, hrE2, haE2, hBE2, hcE2⟩ :=
    extend_layer L2 e2 d2 k D2 hp2 hr2 (L1.source e1 k)
      (bridge_target H21 e1 he1.le d2 he12 k) E1 0 (by simp [hinput1])
  obtain ⟨E3, hpE3, hbE3, hrE3, haE3, hBE3, hcE3⟩ :=
    extend_layer L3 eps d3 k D3 hp3 hr3 (L2.source e2 k)
      (bridge_target H32 e2 he2.le d3 he23 k) E2 L2.degree
      ⟨hpE2, by simpa only [add_zero] using hbE2⟩
  refine ⟨E3, hpE3, hbE3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrE3, hrE2, hrate1]
    ring
  · simpa only [haE3, haE2] using ha1
  · simpa only [hBE3, hBE2] using hb1
  · simpa only [hcE3, hcE2] using hc1
  · rw [haE3, haE2, hBE3, hBE2, hcE3, hcE2]
    simp only [Nat.cast_mul]
    have hlog := congrArg (fun n : ℕ ↦ Real.log (n : ℝ)) hv1
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul] at hlog
    nlinarith [hlog]

#print axioms solution

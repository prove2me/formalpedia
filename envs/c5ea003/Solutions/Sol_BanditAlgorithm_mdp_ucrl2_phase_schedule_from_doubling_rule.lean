-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_phase_schedule_from_doubling_rule
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-03T01:11:44.308459+00:00
-- url     : https://prove2.me/submissions/53f97d7a-f6a3-4855-8374-92c9151551d5

import Definitions.Def_UCRL2Algorithm
import Theorems.Thm_BanditAlgorithm_mdp_doubling_phase_visit_sum_aggregate_le

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm

namespace PhaseSched

variable {S A t : ℕ}

/-! ### Visit counts -/

lemma visitCount_zero (h : MDPTrajectory S A t) (s : Fin S) (a : Fin A) :
    mdpVisitCount h 0 s a = 0 := by
  simp [mdpVisitCount]

lemma visitCount_mono (h : MDPTrajectory S A t) {u w : ℕ} (huw : u ≤ w)
    (s : Fin S) (a : Fin A) :
    mdpVisitCount h u s a ≤ mdpVisitCount h w s a := by
  classical
  refine Finset.card_le_card fun i hi ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 huw, hi.2⟩

lemma visitCount_succ_le (h : MDPTrajectory S A t) (k : ℕ) (s : Fin S) (a : Fin A) :
    mdpVisitCount h (k + 1) s a ≤ mdpVisitCount h k s a + 1 := by
  classical
  have hsub : (univ.filter fun i : Fin t ↦ i.val < k + 1 ∧ h i = (s, a)) ⊆
      (univ.filter fun i : Fin t ↦ i.val < k ∧ h i = (s, a)) ∪
        (univ.filter fun i : Fin t ↦ i.val = k) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi.1 with h1 | h1
    · exact Or.inl ⟨h1, hi.2⟩
    · exact Or.inr h1
  have hone : (univ.filter fun i : Fin t ↦ i.val = k).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact Fin.ext (hx.trans hy.symm)
  simp only [mdpVisitCount]
  calc (univ.filter fun i : Fin t ↦ i.val < k + 1 ∧ h i = (s, a)).card
      ≤ ((univ.filter fun i : Fin t ↦ i.val < k ∧ h i = (s, a)) ∪
          (univ.filter fun i : Fin t ↦ i.val = k)).card := Finset.card_le_card hsub
    _ ≤ (univ.filter fun i : Fin t ↦ i.val < k ∧ h i = (s, a)).card +
          (univ.filter fun i : Fin t ↦ i.val = k).card := Finset.card_union_le _ _
    _ ≤ (univ.filter fun i : Fin t ↦ i.val < k ∧ h i = (s, a)).card + 1 :=
        Nat.add_le_add_left hone _

lemma sum_visitCount_full {n : ℕ} (h : MDPTrajectory S A n) :
    ∑ s, ∑ a, mdpVisitCount h n s a = n := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun i : Fin n ↦ h i) (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin S × Fin A))) (fun x _ ↦ Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  calc ∑ s, ∑ a, mdpVisitCount h n s a
      = ∑ p : Fin S × Fin A, mdpVisitCount h n p.1 p.2 :=
        (Fintype.sum_prod_type (f := fun p : Fin S × Fin A ↦ mdpVisitCount h n p.1 p.2)).symm
    _ = ∑ p : Fin S × Fin A, (univ.filter fun i : Fin n ↦ h i = p).card := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        simp only [mdpVisitCount]
        congr 1
        refine Finset.filter_congr fun i _ ↦ ?_
        simp only [i.isLt, true_and, Prod.mk.eta]
    _ = n := hfib.symm

/-! ### The phase-start function -/

lemma phaseStart_succ (h : MDPTrajectory S A t) (u : ℕ) :
    mdpPhaseStart h (u + 1) =
      if ∃ s a, max 1 (mdpVisitCount h (mdpPhaseStart h u) s a) ≤
          mdpVisitCount h (u + 1) s a - mdpVisitCount h (mdpPhaseStart h u) s a then
        u + 1
      else mdpPhaseStart h u := rfl

lemma phaseStart_le (h : MDPTrajectory S A t) (u : ℕ) : mdpPhaseStart h u ≤ u := by
  induction u with
  | zero => exact le_of_eq rfl
  | succ u ih =>
      rw [phaseStart_succ]
      split
      · exact le_rfl
      · exact ih.trans (Nat.le_succ u)

lemma isStart_succ_iff (h : MDPTrajectory S A t) (u : ℕ) :
    mdpPhaseStart h (u + 1) = u + 1 ↔
      ∃ s a, max 1 (mdpVisitCount h (mdpPhaseStart h u) s a) ≤
        mdpVisitCount h (u + 1) s a - mdpVisitCount h (mdpPhaseStart h u) s a := by
  rw [phaseStart_succ]
  split_ifs with hc
  · exact ⟨fun _ ↦ hc, fun _ ↦ rfl⟩
  · refine ⟨fun he ↦ absurd he ?_, fun he ↦ absurd he hc⟩
    have := phaseStart_le h u
    omega

/-- `mdpPhaseStart` is constant on a stretch free of phase starts. -/
lemma phaseStart_eq_of_gap (h : MDPTrajectory S A t) {v : ℕ}
    (hv : mdpPhaseStart h v = v) :
    ∀ u, v ≤ u → (∀ w, v < w → w ≤ u → mdpPhaseStart h w ≠ w) →
      mdpPhaseStart h u = v := by
  intro u
  induction u with
  | zero => intro hvu _; rw [Nat.le_zero.mp hvu] at hv ⊢; exact hv
  | succ u ih =>
      intro hvu hgap
      rcases Nat.lt_or_ge v (u + 1) with hlt | hge
      · have hvu' : v ≤ u := Nat.lt_succ_iff.mp hlt
        have ih' := ih hvu' fun w hw1 hw2 ↦ hgap w hw1 (hw2.trans (Nat.le_succ u))
        rw [phaseStart_succ]
        split_ifs with hc
        · exact absurd ((isStart_succ_iff h u).mpr hc) (hgap (u + 1) hlt le_rfl)
        · exact ih'
      · have : v = u + 1 := le_antisymm hvu hge
        rw [← this]; exact hv

/-! ### The phase schedule -/

/-- The phase starts strictly after `v` and at most `n`. -/
def phaseStartSet (h : MDPTrajectory S A t) (n v : ℕ) : Finset ℕ :=
  (Finset.Ioc v n).filter fun u ↦ mdpPhaseStart h u = u

/-- The next phase start after `v`, or `n` if there is none. -/
def nextStart (h : MDPTrajectory S A t) (n v : ℕ) : ℕ :=
  if hs : (phaseStartSet h n v).Nonempty then (phaseStartSet h n v).min' hs else n

lemma nextStart_le (h : MDPTrajectory S A t) {n v : ℕ} (hv : v ≤ n) :
    nextStart h n v ≤ n := by
  unfold nextStart
  split_ifs with hs
  · have := (phaseStartSet h n v).min'_mem hs
    simp only [phaseStartSet, Finset.mem_filter, Finset.mem_Ioc] at this
    exact this.1.2
  · exact le_rfl

lemma lt_nextStart (h : MDPTrajectory S A t) {n v : ℕ} (hv : v < n) :
    v < nextStart h n v := by
  unfold nextStart
  split_ifs with hs
  · have := (phaseStartSet h n v).min'_mem hs
    simp only [phaseStartSet, Finset.mem_filter, Finset.mem_Ioc] at this
    exact this.1.1
  · exact hv

lemma nextStart_isStart_or (h : MDPTrajectory S A t) (n v : ℕ) :
    mdpPhaseStart h (nextStart h n v) = nextStart h n v ∨ nextStart h n v = n := by
  unfold nextStart
  split_ifs with hs
  · left
    have := (phaseStartSet h n v).min'_mem hs
    simp only [phaseStartSet, Finset.mem_filter] at this
    exact this.2
  · exact Or.inr rfl

lemma nextStart_min (h : MDPTrajectory S A t) {n v w : ℕ} (hw1 : v < w)
    (hw2 : w < nextStart h n v) : mdpPhaseStart h w ≠ w := by
  intro hPS
  unfold nextStart at hw2
  split_ifs at hw2 with hs
  · have hwn : w ≤ n := le_trans hw2.le
      (by
        have := (phaseStartSet h n v).min'_mem hs
        simp only [phaseStartSet, Finset.mem_filter, Finset.mem_Ioc] at this
        exact this.1.2)
    have hmem : w ∈ phaseStartSet h n v := by
      simp only [phaseStartSet, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hw1, hwn⟩, hPS⟩
    exact absurd ((phaseStartSet h n v).min'_le w hmem) (not_le.mpr hw2)
  · have hmem : w ∈ phaseStartSet h n v := by
      simp only [phaseStartSet, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hw1, hw2.le⟩, hPS⟩
    exact hs ⟨w, hmem⟩

/-- The phase boundaries `τ 0 = 0`, `τ (k+1) =` next phase start. -/
def phaseTime (h : MDPTrajectory S A t) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => nextStart h n (phaseTime h n k)

lemma phaseTime_le (h : MDPTrajectory S A t) (n k : ℕ) : phaseTime h n k ≤ n := by
  induction k with
  | zero => exact Nat.zero_le n
  | succ k ih => exact nextStart_le h ih

lemma phaseTime_stab (h : MDPTrajectory S A t) {n k : ℕ} (hk : phaseTime h n k = n) :
    phaseTime h n (k + 1) = n := by
  have : nextStart h n n = n := by
    unfold nextStart
    split_ifs with hs
    · have := (phaseStartSet h n n).min'_mem hs
      simp only [phaseStartSet, Finset.mem_filter, Finset.mem_Ioc] at this
      omega
    · rfl
  rw [phaseTime, hk, this]

lemma phaseTime_ge (h : MDPTrajectory S A t) (n k : ℕ) :
    phaseTime h n k = n ∨ k ≤ phaseTime h n k := by
  induction k with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ k ih =>
      rcases ih with hk | hk
      · exact Or.inl (phaseTime_stab h hk)
      · rcases eq_or_lt_of_le (phaseTime_le h n k) with he | hlt
        · exact Or.inl (phaseTime_stab h he)
        · exact Or.inr (Nat.succ_le_of_lt (lt_of_le_of_lt hk (lt_nextStart h hlt)))

lemma phaseTime_horizon (h : MDPTrajectory S A t) (n : ℕ) : phaseTime h n n = n :=
  match phaseTime_ge h n n with
  | Or.inl he => he
  | Or.inr hge => le_antisymm (phaseTime_le h n n) hge

end PhaseSched

open PhaseSched

theorem solution
    (S A n : ℕ) (hS : 0 < S) (hA : 0 < A) (hn : 0 < n)
    (h : MDPTrajectory S A n) :
    ∃ (K : ℕ) (τ : ℕ → ℕ),
      τ 0 = 0 ∧ τ K = n ∧ (∀ k, τ k ≤ τ (k + 1)) ∧
      (∀ k < K, τ k < τ (k + 1)) ∧
      (∀ k, K ≤ k → τ k = n) ∧
      (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) ∧
      (∀ k < K, ∀ u ∈ Finset.Ico (τ k) (τ (k + 1)), mdpPhaseStart h u = τ k) ∧
      (∀ k < K, ∀ (s : Fin S) (a : Fin A),
        mdpVisitCount h (τ (k + 1)) s a
          ≤ mdpVisitCount h (τ k) s a + max 1 (mdpVisitCount h (τ k) s a)) := by
  classical
  haveI : Inhabited (Fin S × Fin A) := ⟨(⟨0, hS⟩, ⟨0, hA⟩)⟩
  have hex : ∃ k, phaseTime h n k = n := ⟨n, phaseTime_horizon h n⟩
  obtain ⟨K, hKn, hτK, hmin⟩ : ∃ K, K ≤ n ∧ phaseTime h n K = n ∧
      ∀ j, j < K → phaseTime h n j ≠ n :=
    ⟨Nat.find hex, Nat.find_le (phaseTime_horizon h n), Nat.find_spec hex,
      fun j hj ↦ Nat.find_min hex hj⟩
  -- strict growth before `K`, stabilisation after
  have hlt : ∀ k, k < K → phaseTime h n k < phaseTime h n (k + 1) := fun k hk ↦
    lt_nextStart h (lt_of_le_of_ne (phaseTime_le h n k) (hmin k hk))
  have hstab : ∀ k, K ≤ k → phaseTime h n k = n := by
    intro k hk
    induction k with
    | zero => rw [Nat.le_zero.mp hk] at hτK; exact hτK
    | succ k ih =>
        rcases Nat.lt_or_ge K (k + 1) with hlt' | hge
        · exact phaseTime_stab h (ih (Nat.lt_succ_iff.mp hlt'))
        · rw [← le_antisymm hk hge]; exact hτK
  have hmono : ∀ k, phaseTime h n k ≤ phaseTime h n (k + 1) := by
    intro k
    rcases Nat.lt_or_ge k K with hk | hk
    · exact (hlt k hk).le
    · rw [hstab k hk, hstab (k + 1) (le_trans hk (Nat.le_succ k))]
  -- every phase boundary before `K` is a phase start
  have hstart : ∀ k, k < K → mdpPhaseStart h (phaseTime h n k) = phaseTime h n k := by
    intro k hk
    cases k with
    | zero => rfl
    | succ j =>
        rcases nextStart_isStart_or h n (phaseTime h n j) with hs | hs
        · exact hs
        · exact absurd hs (hmin (j + 1) hk)
  -- `mdpPhaseStart` is constant on each phase
  have hconst : ∀ k, k < K → ∀ u, phaseTime h n k ≤ u → u < phaseTime h n (k + 1) →
      mdpPhaseStart h u = phaseTime h n k := by
    intro k hk u hu1 hu2
    refine phaseStart_eq_of_gap h (hstart k hk) u hu1 fun w hw1 hw2 ↦ ?_
    exact nextStart_min h hw1 (lt_of_le_of_lt hw2 hu2)
  -- the doubling bound on each phase
  have hdouble : ∀ k, k < K → ∀ (s : Fin S) (a : Fin A),
      mdpVisitCount h (phaseTime h n (k + 1)) s a
        ≤ mdpVisitCount h (phaseTime h n k) s a
          + max 1 (mdpVisitCount h (phaseTime h n k) s a) := by
    intro k hk s a
    have hk' := hlt k hk
    obtain ⟨w, hw⟩ : ∃ w, phaseTime h n (k + 1) = w + 1 := ⟨phaseTime h n (k + 1) - 1, by omega⟩
    have hwge : phaseTime h n k ≤ w := by omega
    have hpw : mdpPhaseStart h w = phaseTime h n k := hconst k hk w hwge (by omega)
    rw [hw]
    rcases eq_or_lt_of_le hwge with heq | hgt
    · subst heq
      have h1 := visitCount_succ_le h (phaseTime h n k) s a
      omega
    · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      have hpw' : mdpPhaseStart h w' = phaseTime h n k :=
        hconst k hk w' (by omega) (by omega)
      have hns : mdpPhaseStart h (w' + 1) ≠ w' + 1 := by rw [hpw]; omega
      have hcrit := (not_congr (isStart_succ_iff h w')).mp hns
      push_neg at hcrit
      have hc := hcrit s a
      rw [hpw'] at hc
      have hm := visitCount_mono h (show phaseTime h n k ≤ w' + 1 by omega) s a
      have h1 := visitCount_succ_le h (w' + 1) s a
      omega
  -- the phase count
  have hb0 : ∀ i : Fin S × Fin A,
      ((mdpVisitCount h (phaseTime h n 0) i.1 i.2 : ℝ)) = 0 := by
    intro i; rw [show phaseTime h n 0 = 0 from rfl, visitCount_zero]; norm_num
  have hc0 : ∀ (i : Fin S × Fin A) (k : ℕ),
      (0:ℝ) ≤ (mdpVisitCount h (phaseTime h n (k + 1)) i.1 i.2 : ℝ)
        - (mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ) := by
    intro i k
    have := visitCount_mono h (hmono k) i.1 i.2
    have : ((mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℕ) : ℝ)
        ≤ ((mdpVisitCount h (phaseTime h n (k + 1)) i.1 i.2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hdbl : ∀ (i : Fin S × Fin A) (k : ℕ),
      (mdpVisitCount h (phaseTime h n (k + 1)) i.1 i.2 : ℝ)
        - (mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ)
        ≤ max 1 ((mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ)) := by
    intro i k
    rcases Nat.lt_or_ge k K with hk | hk
    · have hnat := hdouble k hk i.1 i.2
      have hcast : ((mdpVisitCount h (phaseTime h n (k + 1)) i.1 i.2 : ℕ) : ℝ)
          ≤ ((mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℕ) : ℝ)
            + ((max 1 (mdpVisitCount h (phaseTime h n k) i.1 i.2) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at hcast
      linarith
    · rw [hstab k hk, hstab (k + 1) (le_trans hk (Nat.le_succ k))]
      have : (1:ℝ) ≤ max 1 ((mdpVisitCount h n i.1 i.2 : ℝ)) := le_max_left _ _
      linarith
  have htot : ∑ i : Fin S × Fin A, ((mdpVisitCount h (phaseTime h n K) i.1 i.2 : ℝ))
      ≤ (n : ℝ) := by
    rw [hτK]
    have := sum_visitCount_full h
    refine le_of_eq ?_
    calc ∑ i : Fin S × Fin A, ((mdpVisitCount h n i.1 i.2 : ℝ))
        = ((∑ s, ∑ a, mdpVisitCount h n s a : ℕ) : ℝ) := by push_cast [Fintype.sum_prod_type]; rfl
      _ = (n : ℝ) := by rw [this]
  have hagg : ∑ i : Fin S × Fin A, ∑ k ∈ Finset.range K,
        ((mdpVisitCount h (phaseTime h n (k + 1)) i.1 i.2 : ℝ)
          - (mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ))
        / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ)))
      ≤ (Real.sqrt 2 + 1) * Real.sqrt (Fintype.card (Fin S × Fin A) * (n : ℝ)) :=
    BanditAlgorithm.mdp_doubling_phase_visit_sum_aggregate_le _ _ _ _ hb0 hc0
      (fun i k ↦ by ring) hdbl htot
  -- each phase but the last is ended by a doubling pair
  have htrig : ∀ k, k + 1 < K → ∃ q : Fin S × Fin A,
      max 1 (mdpVisitCount h (phaseTime h n k) q.1 q.2)
        ≤ mdpVisitCount h (phaseTime h n (k + 1)) q.1 q.2
          - mdpVisitCount h (phaseTime h n k) q.1 q.2 := by
    intro k hk
    have hkK : k < K := by omega
    have hk' := hlt k hkK
    have hSt := hstart (k + 1) hk
    obtain ⟨w, hw⟩ : ∃ w, phaseTime h n (k + 1) = w + 1 := ⟨phaseTime h n (k + 1) - 1, by omega⟩
    have hpw : mdpPhaseStart h w = phaseTime h n k := hconst k hkK w (by omega) (by omega)
    rw [hw] at hSt
    have hgo := (isStart_succ_iff h w).mp hSt
    rw [hpw] at hgo
    obtain ⟨s, a, hsa⟩ := hgo
    exact ⟨(s, a), by rw [hw]; exact hsa⟩
  choose! q hq using htrig
  have hfnn : ∀ (i : Fin S × Fin A) (k : ℕ),
      (0:ℝ) ≤ ((mdpVisitCount h (phaseTime h n (k + 1)) i.1 i.2 : ℝ)
          - (mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ))
        / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ))) :=
    fun i k ↦ div_nonneg (hc0 i k) (Real.sqrt_nonneg _)
  have hFge : ∀ k, k + 1 < K →
      (1:ℝ) ≤ ((mdpVisitCount h (phaseTime h n (k + 1)) (q k).1 (q k).2 : ℝ)
          - (mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))
        / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))) := by
    intro k hk
    have hqk := hq k hk
    have hm := visitCount_mono h (hmono k) (q k).1 (q k).2
    have hnat : mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2
        + max 1 (mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2)
        ≤ mdpVisitCount h (phaseTime h n (k + 1)) (q k).1 (q k).2 := by omega
    have hcast : ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℕ) : ℝ)
        + ((max 1 (mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2) : ℕ) : ℝ)
        ≤ ((mdpVisitCount h (phaseTime h n (k + 1)) (q k).1 (q k).2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    have hM1 : (1:ℝ) ≤ max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ)) :=
      le_max_left _ _
    have hsq : (1:ℝ) ≤ Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))) := by
      have := Real.sqrt_le_sqrt hM1
      rwa [Real.sqrt_one] at this
    have hspos : (0:ℝ) < Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))) := by
      linarith
    calc (1:ℝ) ≤ Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))) := hsq
      _ = max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))
            / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))) :=
          Real.div_sqrt.symm
      _ ≤ _ := by gcongr; linarith
  have hlow : ((K - 1 : ℕ) : ℝ) ≤ ∑ i : Fin S × Fin A, ∑ k ∈ Finset.range K,
        ((mdpVisitCount h (phaseTime h n (k + 1)) i.1 i.2 : ℝ)
          - (mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ))
        / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) i.1 i.2 : ℝ))) := by
    have hinj : Set.InjOn (fun k ↦ ((q k), k)) (Finset.range (K - 1) : Finset ℕ) :=
      fun x _ y _ hxy ↦ congrArg Prod.snd hxy
    have himg : ((Finset.range (K - 1)).image fun k ↦ ((q k), k)) ⊆
        (Finset.univ : Finset (Fin S × Fin A)) ×ˢ Finset.range K := by
      intro p hp
      simp only [Finset.mem_image, Finset.mem_range] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
      omega
    calc ((K - 1 : ℕ) : ℝ) = ∑ _k ∈ Finset.range (K - 1), (1:ℝ) := by simp
      _ ≤ ∑ k ∈ Finset.range (K - 1),
            ((mdpVisitCount h (phaseTime h n (k + 1)) (q k).1 (q k).2 : ℝ)
              - (mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))
            / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n k) (q k).1 (q k).2 : ℝ))) := by
          refine Finset.sum_le_sum fun k hk ↦ hFge k ?_
          simp only [Finset.mem_range] at hk
          omega
      _ = ∑ p ∈ ((Finset.range (K - 1)).image fun k ↦ ((q k), k)),
            ((mdpVisitCount h (phaseTime h n (p.2 + 1)) (p.1).1 (p.1).2 : ℝ)
              - (mdpVisitCount h (phaseTime h n p.2) (p.1).1 (p.1).2 : ℝ))
            / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n p.2) (p.1).1 (p.1).2 : ℝ))) :=
          by rw [Finset.sum_image hinj]
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin S × Fin A)) ×ˢ Finset.range K,
            ((mdpVisitCount h (phaseTime h n (p.2 + 1)) (p.1).1 (p.1).2 : ℝ)
              - (mdpVisitCount h (phaseTime h n p.2) (p.1).1 (p.1).2 : ℝ))
            / Real.sqrt (max 1 ((mdpVisitCount h (phaseTime h n p.2) (p.1).1 (p.1).2 : ℝ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ ↦ hfnn p.1 p.2
      _ = _ := Finset.sum_product _ _ _
  have hcard : ((Fintype.card (Fin S × Fin A) : ℝ)) * (n : ℝ) = (S : ℝ) * A * n := by
    simp [Fintype.card_prod]
  have hmain : ((K - 1 : ℕ) : ℝ) ≤ (Real.sqrt 2 + 1) * Real.sqrt ((S : ℝ) * A * n) := by
    refine hlow.trans (hagg.trans_eq ?_)
    rw [hcard]
  -- assemble
  have hS1 : (1:ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hA1 : (1:ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSA1 : (1:ℝ) ≤ (S : ℝ) * A := by nlinarith
  have hSAn1 : (1:ℝ) ≤ (S : ℝ) * A * n := by
    calc (1:ℝ) = 1 * 1 := by norm_num
      _ ≤ ((S : ℝ) * A) * n := mul_le_mul hSA1 hn1 (by norm_num) (by linarith)
      _ = (S : ℝ) * A * n := rfl
  have hKbound : (K : ℝ) ≤ 3 * Real.sqrt ((S : ℝ) * A * n) := by
    have hK1 : (K : ℝ) - 1 ≤ ((K - 1 : ℕ) : ℝ) := by
      cases K with
      | zero => simp
      | succ K' => push_cast; simp
    by_cases hsmall : n ≤ 3
    · have h1 : (1:ℝ) ≤ Real.sqrt ((S : ℝ) * A * n) := by
        have := Real.sqrt_le_sqrt hSAn1
        rwa [Real.sqrt_one] at this
      have hK3 : (K : ℝ) ≤ 3 := by exact_mod_cast (by omega : K ≤ 3)
      linarith
    · push_neg at hsmall
      have hn4 : (4:ℝ) ≤ (n : ℝ) := by exact_mod_cast hsmall
      have h4 : (4:ℝ) ≤ (S : ℝ) * A * n := by
        calc (4:ℝ) = 1 * 4 := by norm_num
          _ ≤ ((S : ℝ) * A) * n := mul_le_mul hSA1 hn4 (by norm_num) (by linarith)
          _ = (S : ℝ) * A * n := rfl
      have h2 : (2:ℝ) ≤ Real.sqrt ((S : ℝ) * A * n) := by
        have hle := Real.sqrt_le_sqrt h4
        rwa [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at hle
      have hs2 : Real.sqrt 2 ≤ 1.5 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have hprod : (Real.sqrt 2 + 1) * Real.sqrt ((S : ℝ) * A * n)
          ≤ 2.5 * Real.sqrt ((S : ℝ) * A * n) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      linarith
  refine ⟨K, phaseTime h n, rfl, hτK, hmono, hlt, hstab, hKbound, ?_, hdouble⟩
  intro k hk u hu
  simp only [Finset.mem_Ico] at hu
  exact hconst k hk u hu.1 hu.2

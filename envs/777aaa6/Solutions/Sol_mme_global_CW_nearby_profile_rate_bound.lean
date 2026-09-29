-- Prove2me | solution 1 for mme_global_CW_nearby_profile_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:51:08.935777+00:00
-- url     : https://prove2.me/submissions/0fbcec3c-eff7-4ef0-84f6-e45e34c2aad8

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Theorems.Thm_mme_entropy_penalty_upper_stability
open BigOperators MME MME.GlobalCW MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000

private theorem mass_continuous {W : Type*} [Fintype W] :
    Continuous (massEntropy (W := W)) := by
  unfold massEntropy entropy
  exact (continuous_finset_sum _ (fun w _ ↦ Real.continuous_negMulLog.comp (continuous_apply w))).sub
    (Real.continuous_negMulLog.comp (continuous_finset_sum _ (fun w _ ↦ continuous_apply w)))

private theorem coarse_continuous {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} (i : Fin 3) (r : Fin R) :
    Continuous (fun p : EntropyProfile degree R bounds W ↦ p.coarse i r) := by
  apply mass_continuous.comp
  apply continuous_pi
  intro j
  exact continuous_finset_sum _ (fun c _ ↦
    (continuous_apply c.val).comp ((continuous_apply r).comp continuous_fst))

private theorem words_continuous {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (i : Fin 3) (r : Fin R) :
    Continuous (fun p : EntropyProfile degree R bounds W ↦ p.words i r) := by
  apply continuous_finset_sum
  intro j _
  apply mass_continuous.comp
  apply continuous_pi
  intro w
  apply continuous_finset_sum
  intro c _
  by_cases hc : c.val i = j
  · simp only [hc,if_true]
    exact (continuous_apply w).comp ((continuous_apply (⟨r,c⟩ : Cell degree R bounds)).comp
      ((continuous_apply i).comp continuous_snd))
  · simp only [hc,if_false]
    exact continuous_const

private theorem compat_continuous {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (i : Fin 2) (r : Fin R) :
    Continuous (fun p : EntropyProfile degree R bounds W ↦ p.compat i r) := by
  apply Continuous.add
  · apply continuous_finset_sum
    intro c _
    apply mass_continuous.comp
    apply continuous_pi
    intro w
    exact (continuous_apply w).comp ((continuous_apply (⟨r,c.val⟩ : Cell degree R bounds)).comp
      ((continuous_apply (yzMode i)).comp continuous_snd))
  · apply continuous_finset_sum
    intro j _
    apply mass_continuous.comp
    apply continuous_pi
    intro w
    apply continuous_finset_sum
    intro c _
    by_cases hc : ¬ yzBoundary i ⟨r,c⟩ ∧ c.val (yzMode i) = j
    · simp only [hc,if_true]
      exact (continuous_apply w).comp ((continuous_apply (⟨r,c⟩ : Cell degree R bounds)).comp
        ((continuous_apply (yzMode i)).comp continuous_snd))
    · simp only [hc,if_false]
      exact continuous_const

theorem solution {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (p : EntropyProfile degree R bounds W)
    (hpos : ∀ r c, 0 ≤ p.1 r c) (hmass : ∀ r, ∑ c, p.1 r c = 1)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ q : EntropyProfile degree R bounds W,
      (∀ r c, 0 ≤ q.1 r c) → (∀ r, ∑ c, q.1 r c = 1) →
      (∀ r c, |q.1 r c - p.1 r c| ≤ eps) →
      (∀ i c w, |q.2 i c w - p.2 i c w| ≤ eps) →
      ∀ weights : Fin R → ℝ, (∀ r, 0 ≤ weights r) →
        p.rate weights - delta * (∑ r, weights r) ≤ q.rate weights := by
  classical
  by_cases hR : R = 0
  · subst R
    exact ⟨1,by norm_num,by intros; simp [EntropyProfile.rate]⟩
  haveI : Nonempty (Fin R) := ⟨⟨0,Nat.pos_of_ne_zero hR⟩⟩
  let g : EntropyProfile degree R bounds W → Fin 3 × Fin R → ℝ := fun x a ↦
    ![x.coarse 0 a.2, x.coarse 1 a.2 + x.words 1 a.2 - x.compat 0 a.2,
      x.coarse 2 a.2 + x.words 2 a.2 - x.compat 1 a.2] a.1
  have hg : Continuous g := by
    apply continuous_pi
    intro a
    rcases a with ⟨i,r⟩
    fin_cases i
    · exact coarse_continuous 0 r
    · exact ((coarse_continuous 1 r).add (words_continuous 1 r)).sub (compat_continuous 0 r)
    · exact ((coarse_continuous 2 r).add (words_continuous 2 r)).sub (compat_continuous 1 r)
  obtain ⟨ec,hec,hc⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := p))
    (delta/2) (half_pos hdelta)
  choose ep hep hp using (fun r ↦ mme_entropy_penalty_upper_stability (p.1 r)
    (hpos r) (hmass r) (delta/2) (half_pos hdelta))
  let e := (Finset.univ : Finset (Fin R)).inf' Finset.univ_nonempty ep
  have he : 0 < e := (Finset.lt_inf'_iff _).mpr (fun r _ ↦ hep r)
  have hle (r : Fin R) : e ≤ ep r := Finset.inf'_le ep (Finset.mem_univ r)
  refine ⟨min e (ec/2),lt_min he (half_pos hec),?_⟩
  intro q hqp hqm hqa hqw weights hw
  have hd : dist q p < ec := by
    rw [Prod.dist_eq]
    apply max_lt
    · apply (dist_pi_lt_iff hec).mpr
      intro r
      apply (dist_pi_lt_iff hec).mpr
      intro c
      rw [Real.dist_eq]
      exact ((hqa r c).trans (min_le_right _ _)).trans_lt (half_lt_self hec)
    · apply (dist_pi_lt_iff hec).mpr
      intro i
      apply (dist_pi_lt_iff hec).mpr
      intro c
      apply (dist_pi_lt_iff hec).mpr
      intro w
      rw [Real.dist_eq]
      exact ((hqw i c w).trans (min_le_right _ _)).trans_lt (half_lt_self hec)
  have hcg (i : Fin 3) (r : Fin R) : |g q (i,r) - g p (i,r)| < delta/2 := by
    simpa only [Real.dist_eq] using (dist_pi_lt_iff (half_pos hdelta)).mp (hc hd) (i,r)
  have hpen (r : Fin R) := hp r (q.1 r) (hqp r) (hqm r)
    (fun c ↦ (hqa r c).trans ((min_le_left _ _).trans (hle r)))
  have hx (r : Fin R) :
      p.coarse 0 r - Real.log 2 * entropyPenalty (p.1 r) - delta ≤
      q.coarse 0 r - Real.log 2 * entropyPenalty (q.1 r) := by
    have h := (abs_lt.mp (hcg 0 r)).1
    change -(delta/2) < q.coarse 0 r - p.coarse 0 r at h
    linarith [hpen r]
  have hyz (i : Fin 2) (r : Fin R) :
      p.coarse (yzMode i) r + p.words (yzMode i) r - p.compat i r - delta ≤
      q.coarse (yzMode i) r + q.words (yzMode i) r - q.compat i r := by
    fin_cases i
    · have h := (abs_lt.mp (hcg 1 r)).1
      change -(delta/2) < (q.coarse 1 r + q.words 1 r - q.compat 0 r) -
        (p.coarse 1 r + p.words 1 r - p.compat 0 r) at h
      change p.coarse 1 r + p.words 1 r - p.compat 0 r - delta ≤ q.coarse 1 r + q.words 1 r - q.compat 0 r
      linarith
    · have h := (abs_lt.mp (hcg 2 r)).1
      change -(delta/2) < (q.coarse 2 r + q.words 2 r - q.compat 1 r) -
        (p.coarse 2 r + p.words 2 r - p.compat 1 r) at h
      change p.coarse 2 r + p.words 2 r - p.compat 1 r - delta ≤ q.coarse 2 r + q.words 2 r - q.compat 1 r
      linarith
  have sum_bound (a b : Fin R → ℝ) (hab : ∀ r, a r - delta ≤ b r) :
      (∑ r, weights r * a r) - delta * (∑ r, weights r) ≤ ∑ r, weights r * b r := by
    calc
      _ = ∑ r, weights r * (a r - delta) := by
        simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun r _ ↦ mul_le_mul_of_nonneg_left (hab r) (hw r))
  have hX := sum_bound _ _ hx
  have hY := sum_bound _ _ (hyz 0)
  have hZ := sum_bound _ _ (hyz 1)
  unfold EntropyProfile.rate
  rw [← min_sub_sub_right,← min_sub_sub_right]
  exact min_le_min hX (min_le_min hY hZ)

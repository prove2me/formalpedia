-- Prove2me | solution 1 for BanditAlgorithm.armStoppedCenteredSum_eq_firstRewardsMean
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T01:09:37.586105+00:00
-- url     : https://prove2.me/submissions/c9bdda29-714f-4f8f-97f7-dbdaad11cd60

import Definitions.Def_ThompsonSampling
import Definitions.Def_ucbStoppedCenteredSum

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

private theorem armPullCount_snoc_fs {k m : ℕ}
    (i : Fin k) (h : BanditHistory k m) (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add]
  have hsum {q : ℕ} (g : BanditHistory k q) :
      (armPullCount i g : ℝ) =
        ∑ t, if (g t).1 = i then 1 else 0 := by
    classical
    rw [armPullCount]
    have hs : {t | (g t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (g t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin q ↦ (g t).1 = i) Finset.univ).symm
  rw [hsum, hsum h, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armPullCountBefore_castSucc_snoc_fs {k m : ℕ}
    (i : Fin k) (h : BanditHistory k m) (z : Fin k × ℝ) (t : Fin m) :
    armPullCountBefore i t.castSucc
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCountBefore i t h := by
  classical
  apply Nat.cast_injective (R := ℝ)
  have hsum {q : ℕ} (r : Fin q) (g : BanditHistory k q) :
      (armPullCountBefore i r g : ℝ) =
        ∑ u, if u < r ∧ (g u).1 = i then 1 else 0 := by
    unfold armPullCountBefore
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp
  rw [hsum, hsum t h, Fin.sum_univ_castSucc]
  have hnot : ¬(Fin.last m < t.castSucc) := by
    simp [Fin.lt_iff_val_lt_val]
  simp [hnot]

private theorem armPullCountBefore_last_snoc_fs {k m : ℕ}
    (i : Fin k) (h : BanditHistory k m) (z : Fin k × ℝ) :
    armPullCountBefore i (Fin.last m)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h := by
  classical
  apply Nat.cast_injective (R := ℝ)
  have hbefore :
      (armPullCountBefore i (Fin.last m)
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) : ℝ) =
        ∑ u, if u < Fin.last m ∧
          ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) u).1 = i
          then 1 else 0 := by
    unfold armPullCountBefore
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp
  have hpull :
      (armPullCount i h : ℝ) =
        ∑ u, if (h u).1 = i then 1 else 0 := by
    rw [armPullCount]
    have hs : {u | (h u).1 = i}.toFinset =
        Finset.univ.filter (fun u ↦ (h u).1 = i) := by
      ext u
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun u : Fin m ↦ (h u).1 = i) Finset.univ).symm
  rw [hbefore, hpull, Fin.sum_univ_castSucc]
  simp

private noncomputable def armFirstCenteredSum_fs {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (s : ℕ)
    (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i ∧ armPullCountBefore i t h < s then
    (h t).2 - banditArmMean ν i else 0

private theorem armFirstCenteredSum_snoc_fs {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (s : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armFirstCenteredSum_fs ν i s
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armFirstCenteredSum_fs ν i s h +
      if z.1 = i ∧ armPullCount i h < s then
          z.2 - banditArmMean ν i else 0 := by
  classical
  simp only [armFirstCenteredSum_fs, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Fin.snoc_castSucc, armPullCountBefore_castSucc_snoc_fs]
  · rw [Fin.snoc_last, armPullCountBefore_last_snoc_fs]

private noncomputable def armFirstCount_fs {k n : ℕ}
    (i : Fin k) (s : ℕ) (h : BanditHistory k n) : ℕ :=
  ∑ t, if (h t).1 = i ∧ armPullCountBefore i t h < s then 1 else 0

private theorem armFirstCount_snoc_fs {k m : ℕ}
    (i : Fin k) (s : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    armFirstCount_fs i s
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armFirstCount_fs i s h +
        if z.1 = i ∧ armPullCount i h < s then 1 else 0 := by
  classical
  simp only [armFirstCount_fs, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Fin.snoc_castSucc, armPullCountBefore_castSucc_snoc_fs]
  · rw [Fin.snoc_last, armPullCountBefore_last_snoc_fs]

private theorem armFirstCount_eq_min_fs {k m : ℕ}
    (i : Fin k) (s : ℕ) (h : BanditHistory k m) :
    armFirstCount_fs i s h = min (armPullCount i h) s := by
  induction m with
  | zero => simp [armFirstCount_fs, armPullCount]
  | succ m ih =>
      rw [← Fin.snoc_init_self h]
      rw [armFirstCount_snoc_fs, armPullCount_snoc_fs, ih (Fin.init h)]
      by_cases hi : (h (Fin.last m)).1 = i
      · by_cases hc : armPullCount i (Fin.init h) < s
        · simp [hi, hc]
          omega
        · simp [hi, hc]
          omega
      · simp [hi]

private theorem armStoppedCenteredSum_snoc_fs {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (s : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i s (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i s m h +
        if armPullCount i h < s ∧ z.1 = i then
          z.2 - banditArmMean ν i else 0 := by
  simp [armStoppedCenteredSum]

private theorem armStoppedCenteredSum_eq_firstCenteredSum_fs
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (s : ℕ)
    (h : BanditHistory k m) :
    armStoppedCenteredSum ν i s m h =
      armFirstCenteredSum_fs ν i s h := by
  induction m with
  | zero => simp [armStoppedCenteredSum, armFirstCenteredSum_fs]
  | succ m ih =>
      rw [← Fin.snoc_init_self h]
      rw [armStoppedCenteredSum_snoc_fs, armFirstCenteredSum_snoc_fs,
        ih (Fin.init h)]
      by_cases ha : armPullCount i (Fin.init h) < s
      · by_cases hi : (h (Fin.last m)).1 = i <;> simp [ha, hi, and_comm]
      · simp [ha]

private theorem armFirstCenteredSum_eq_fs
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (s : ℕ)
    (h : BanditHistory k m) (hs : 0 < s)
    (hcount : s ≤ armPullCount i h) :
    armFirstCenteredSum_fs ν i s h =
      (s : ℝ) * (armFirstRewardsMean i s h - banditArmMean ν i) := by
  classical
  let S : Finset (Fin m) :=
    Finset.univ.filter
      (fun t : Fin m ↦ (h t).1 = i ∧ armPullCountBefore i t h < s)
  have hcard : S.card = s := by
    have hS :
        S.card = armFirstCount_fs i s h := by
      unfold S armFirstCount_fs
      rw [Finset.card_filter]
    rw [hS, armFirstCount_eq_min_fs, min_eq_right hcount]
  have hsum :
      armFirstCenteredSum_fs ν i s h =
        ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    unfold armFirstCenteredSum_fs S
    rw [← Finset.sum_filter]
  rw [hsum]
  have hmean :
      armFirstRewardsMean i s h =
        (∑ t ∈ S, (h t).2) / (s : ℝ) := by
    unfold armFirstRewardsMean
    congr 2
  rw [hmean]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  field_simp

theorem armStoppedCenteredSum_eq_firstRewardsMean
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (s : ℕ)
    (h : BanditHistory k m) (hs : 0 < s)
    (hcount : s ≤ armPullCount i h) :
    armStoppedCenteredSum ν i s m h =
      (s : ℝ) *
        (armFirstRewardsMean i s h - banditArmMean ν i) := by
  rw [armStoppedCenteredSum_eq_firstCenteredSum_fs]
  exact armFirstCenteredSum_eq_fs ν i s h hs hcount

end BanditAlgorithm

theorem solution
    {k m : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (i : Fin k) (s : ℕ)
    (h : BanditAlgorithm.BanditHistory k m) (hs : 0 < s)
    (hcount : s ≤ BanditAlgorithm.armPullCount i h) :
    BanditAlgorithm.armStoppedCenteredSum ν i s m h =
      (s : ℝ) *
        (BanditAlgorithm.armFirstRewardsMean i s h -
          BanditAlgorithm.banditArmMean ν i) :=
  BanditAlgorithm.armStoppedCenteredSum_eq_firstRewardsMean
    ν i s h hs hcount

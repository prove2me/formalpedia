-- Prove2me | Definitions.Def_KServer_race_total
-- name    : KServer_race_total
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T18:45:14.657882+00:00
-- url     : https://prove2.me/theorems/0bd44401-03f7-44d9-b8b9-478c3371474d
-- title:
--   Pathwise decomposition of the race total
-- statement:
--   Pathwise accounting for the race chunk system: partial size sums $\mathrm{preSum}$ of a chunk system with their monotonicity, stability and bounds; the identities expressing the consumed left/right masses as partial sums at the coin counts; and the exact pathwise decomposition of the total race size into the head total, the per-coin claimed minima, the surviving side's future mass beyond its consumed prefix (minus one sacrificed chunk), and the closing total minus its sacrificed first chunk. Includes the pathwise bounds: each coin claim is at least half the conditionally expected consumption up to $\varepsilon/2$ (the two clamped claims differ by at most $\varepsilon$), the survivor part dominates the minimum of the two side totals minus the consumed minimum and one clamp $c_B$, and range bounds for all tail parts.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt
import Definitions.Def_KServer_race_cost1
import Definitions.Def_KServer_race_cost2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Decomp

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Partial size sums of a chunk system. -/
noncomputable def preSum (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, C.sizeN i ωc

theorem preSum_total (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω) :
    preSum C ωc C.m = ∑ i, C.size ωc i := by
  unfold preSum
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ChunkSystemB.sizeN
  rw [dif_pos i.isLt]

theorem preSum_le (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    {a b : ℕ} (hab : a ≤ b) : preSum C ωc a ≤ preSum C ωc b := by
  unfold preSum
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega) fun i _ _ => ?_
  exact C.sizeN_nonneg (le_refl 0) i ωc

theorem preSum_nonneg (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (n : ℕ) : 0 ≤ preSum C ωc n :=
  Finset.sum_nonneg fun i _ => C.sizeN_nonneg (le_refl 0) i ωc

theorem preSum_stable (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    {n : ℕ} (hn : C.m ≤ n) : preSum C ωc n = preSum C ωc C.m := by
  unfold preSum
  simp only [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le C.m) hn]
  have h2 : ∑ i ∈ Finset.Ico C.m n, C.sizeN i ωc = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    unfold ChunkSystemB.sizeN
    rw [dif_neg (by omega)]
  rw [h2, add_zero]

theorem preSum_ub (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (hcB : 0 ≤ cB) (n : ℕ) : preSum C ωc n ≤ C.m * cB := by
  have h1 : preSum C ωc n ≤ preSum C ωc (max n C.m) :=
    preSum_le C ωc (le_max_left _ _)
  have h2 : preSum C ωc (max n C.m) = preSum C ωc C.m :=
    preSum_stable C ωc (le_max_right _ _)
  rw [h2] at h1
  refine le_trans h1 ?_
  unfold preSum
  have h3 : ∀ i ∈ Finset.range C.m, C.sizeN i ωc ≤ cB := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact C.sizeN_le (hm := hi) ωc
  refine le_trans (Finset.sum_le_sum h3) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The consumed left size is the left partial sum at the count. -/
theorem sumL_eq_preSum (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (ω : RΩ A BL BR CC κ) :
    sumL A BL BR CC κ ω = preSum BL ω.2.1 (cntL ω.2.2.2.2 κ) := by
  suffices h : ∀ j : ℕ, j ≤ κ →
      (∑ i ∈ Finset.univ.filter (fun i : Fin κ => (i : ℕ) < j),
        if ω.2.2.2.2 i then nextL A BL BR CC κ ω (i : ℕ) else 0)
      = preSum BL ω.2.1 (cntL ω.2.2.2.2 j) by
    have h2 := h κ (le_refl κ)
    rw [show (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < κ))
      = Finset.univ from by
        ext i
        simp [i.isLt]] at h2
    exact h2
  intro j
  induction j with
  | zero =>
    intro _
    rw [cntL_zero]
    have hempty : (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < 0))
        = ∅ := by
      ext i
      simp
    rw [hempty, Finset.sum_empty]
    rfl
  | succ j ih =>
    intro hj
    have hjκ : j < κ := by omega
    have hsplit : (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < j + 1))
        = insert (⟨j, hjκ⟩ : Fin κ)
          (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < j)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hi
        by_cases hij : (i : ℕ) = j
        · left
          exact Fin.ext hij
        · right
          omega
      · intro hi
        rcases hi with hi | hi
        · rw [hi]
          exact Nat.lt_succ_self j
        · omega
    rw [hsplit, Finset.sum_insert (by simp)]
    rw [ih (by omega)]
    rw [cntL_succ ω.2.2.2.2 hjκ]
    by_cases hb : ω.2.2.2.2 ⟨j, hjκ⟩
    · rw [if_pos hb, if_pos hb]
      unfold preSum nextL
      rw [Finset.sum_range_succ]
      ring
    · rw [if_neg hb, if_neg (by
        intro hcon
        exact hb (by rw [hcon])), Nat.add_zero, zero_add]
  
theorem sumR_eq_preSum (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (ω : RΩ A BL BR CC κ) :
    sumR A BL BR CC κ ω = preSum BR ω.2.2.1 (cntR ω.2.2.2.2 κ) := by
  suffices h : ∀ j : ℕ, j ≤ κ →
      (∑ i ∈ Finset.univ.filter (fun i : Fin κ => (i : ℕ) < j),
        if ω.2.2.2.2 i then 0 else nextR A BL BR CC κ ω (i : ℕ))
      = preSum BR ω.2.2.1 (cntR ω.2.2.2.2 j) by
    have h2 := h κ (le_refl κ)
    rw [show (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < κ))
      = Finset.univ from by
        ext i
        simp [i.isLt]] at h2
    exact h2
  intro j
  induction j with
  | zero =>
    intro _
    rw [cntR_zero]
    have hempty : (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < 0))
        = ∅ := by
      ext i
      simp
    rw [hempty, Finset.sum_empty]
    rfl
  | succ j ih =>
    intro hj
    have hjκ : j < κ := by omega
    have hsplit : (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < j + 1))
        = insert (⟨j, hjκ⟩ : Fin κ)
          (Finset.univ.filter (fun i : Fin κ => (i : ℕ) < j)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hi
        by_cases hij : (i : ℕ) = j
        · left
          exact Fin.ext hij
        · right
          omega
      · intro hi
        rcases hi with hi | hi
        · rw [hi]
          exact Nat.lt_succ_self j
        · omega
    rw [hsplit, Finset.sum_insert (by simp)]
    rw [ih (by omega)]
    rw [cntR_succ ω.2.2.2.2 hjκ]
    by_cases hb : ω.2.2.2.2 ⟨j, hjκ⟩
    · rw [if_pos hb, if_neg (by
        intro hcon
        rw [hb] at hcon
        exact Bool.true_eq_false.mp hcon), Nat.add_zero, zero_add]
    · rw [if_neg hb, if_pos (by
        cases hcon : ω.2.2.2.2 ⟨j, hjκ⟩
        · rfl
        · exact absurd hcon hb)]
      unfold preSum nextR
      rw [Finset.sum_range_succ]
      ring

end Decomp

section Pathwise

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Splitting a range sum at an intermediate point. -/
theorem sum_range_split (a b : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (a + b), f i
      = (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.range b, f (a + i) := by
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive f (Nat.zero_le a) (Nat.le_add_right a b),
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, Nat.sub_zero, Nat.zero_add]

theorem preSum_succ (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (n : ℕ) : preSum C ωc (n + 1) = preSum C ωc n + C.sizeN n ωc :=
  Finset.sum_range_succ _ n

theorem preSum_le_total (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (n : ℕ) : preSum C ωc n ≤ preSum C ωc C.m := by
  rcases le_total n C.m with h | h
  · exact preSum_le C ωc h
  · rw [preSum_stable C ωc h]

theorem sizeN_le_cB (C : ChunkSystemB X s t 0 cB T pe mL) (hcB : 0 ≤ cB)
    (n : ℕ) (ωc : C.Ω) : C.sizeN n ωc ≤ cB := by
  by_cases hn : n < C.m
  · exact C.sizeN_le hn ωc
  · unfold ChunkSystemB.sizeN
    rw [dif_neg hn]
    exact hcB

/-- The surviving-side middle segment of the tail sums to the survivor's
future mass beyond the consumed prefix (plus one sacrificed chunk). -/
theorem sterm_sum (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    {cnt K : ℕ} (hcm : cnt ≤ C.m) (hK : C.m - cnt ≤ K) :
    ∑ k ∈ Finset.range K,
        (if 0 < k ∧ k < C.m - cnt then C.sizeN (cnt + k) ωc else 0)
      = preSum C ωc C.m - preSum C ωc (cnt + 1) := by
  by_cases hR : C.m - cnt = 0
  · have h0 : ∀ k ∈ Finset.range K,
        (if 0 < k ∧ k < C.m - cnt then C.sizeN (cnt + k) ωc else 0) = 0 := by
      intro k _
      rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl h0, Finset.sum_const, smul_zero]
    have hcnt : cnt = C.m := by omega
    rw [hcnt, preSum_stable C ωc (n := C.m + 1) (by omega), sub_self]
  · have hsub : Finset.Ico 1 (C.m - cnt) ⊆ Finset.range K := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_range]
      omega
    have hzero : ∀ x ∈ Finset.range K, x ∉ Finset.Ico 1 (C.m - cnt) →
        (if 0 < x ∧ x < C.m - cnt then C.sizeN (cnt + x) ωc else 0) = 0 := by
      intro x _ hnx
      rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hnx
      rw [if_neg (by omega)]
    rw [← Finset.sum_subset hsub hzero]
    have hpos : ∀ k ∈ Finset.Ico 1 (C.m - cnt),
        (if 0 < k ∧ k < C.m - cnt then C.sizeN (cnt + k) ωc else 0)
          = C.sizeN (cnt + k) ωc := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hpos]
    have key : preSum C ωc (cnt + 1)
        + ∑ i ∈ Finset.Ico (cnt + 1) C.m, C.sizeN i ωc
        = preSum C ωc C.m := by
      unfold preSum
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive _ (by omega) (by omega)
    rw [← key, add_sub_cancel_left,
      Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
      show C.m - cnt - 1 = C.m - (cnt + 1) from by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show cnt + (1 + i) = cnt + 1 + i from by omega]

/-- The closing-system segment of the tail sums to the closing total minus
the sacrificed first chunk. -/
theorem cterm_sum (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    {R K : ℕ} (hRK : R + C.m ≤ K) :
    ∑ k ∈ Finset.range K, (if R < k then C.sizeN (k - R) ωc else 0)
      = preSum C ωc C.m - preSum C ωc 1 := by
  by_cases hm : C.m = 0
  · have h0 : ∀ k ∈ Finset.range K,
        (if R < k then C.sizeN (k - R) ωc else 0) = 0 := by
      intro k _
      by_cases hRk : R < k
      · rw [if_pos hRk]
        unfold ChunkSystemB.sizeN
        rw [dif_neg (by omega)]
      · rw [if_neg hRk]
    rw [Finset.sum_congr rfl h0, Finset.sum_const, smul_zero,
      preSum_stable C ωc (by omega : C.m ≤ 1), sub_self]
  · have hsub : Finset.Ico (R + 1) (R + C.m) ⊆ Finset.range K := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_range]
      omega
    have hzero : ∀ x ∈ Finset.range K, x ∉ Finset.Ico (R + 1) (R + C.m) →
        (if R < x then C.sizeN (x - R) ωc else 0) = 0 := by
      intro x _ hnx
      rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hnx
      by_cases hRx : R < x
      · rw [if_pos hRx]
        unfold ChunkSystemB.sizeN
        rw [dif_neg (by omega)]
      · rw [if_neg hRx]
    rw [← Finset.sum_subset hsub hzero]
    have hpos : ∀ k ∈ Finset.Ico (R + 1) (R + C.m),
        (if R < k then C.sizeN (k - R) ωc else 0) = C.sizeN (k - R) ωc := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hpos]
    have key : preSum C ωc 1 + ∑ i ∈ Finset.Ico 1 C.m, C.sizeN i ωc
        = preSum C ωc C.m := by
      unfold preSum
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive _ (by omega) (by omega)
    rw [← key, add_sub_cancel_left,
      Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
      show R + C.m - (R + 1) = C.m - 1 from by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show R + 1 + i - R = 1 + i from by omega]

/-- The coin-phase claimed size at step `j`. -/
noncomputable def coinTerm (ω : RΩ A BL BR CC κ) (j : ℕ) : ℝ :=
  min (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
       * nextL A BL BR CC κ ω j)
      (probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
       * nextR A BL BR CC κ ω j)

/-- The survivor tail contribution. -/
noncomputable def survPart (ω : RΩ A BL BR CC κ) : ℝ :=
  if survL A BL BR CC κ ω then
    preSum BL ω.2.1 BL.m - preSum BL ω.2.1 (cntL ω.2.2.2.2 κ + 1)
  else
    preSum BR ω.2.2.1 BR.m - preSum BR ω.2.2.1 (cntR ω.2.2.2.2 κ + 1)

/-- The closing-system tail contribution. -/
noncomputable def ccPart (ω : RΩ A BL BR CC κ) : ℝ :=
  preSum CC ω.2.2.2.1 CC.m - preSum CC ω.2.2.2.1 1

theorem survL_true_iff (ω : RΩ A BL BR CC κ) :
    survL A BL BR CC κ ω = true
      ↔ sumL A BL BR CC κ ω ≤ sumR A BL BR CC κ ω := by
  unfold survL
  split
  · next h => exact iff_of_true rfl h
  · next h => exact iff_of_false Bool.false_ne_true h

theorem survL_false_le (ω : RΩ A BL BR CC κ)
    (hs : survL A BL BR CC κ ω = false) :
    sumR A BL BR CC κ ω ≤ sumL A BL BR CC κ ω := by
  unfold survL at hs
  by_cases h : sumL A BL BR CC κ ω ≤ sumR A BL BR CC κ ω
  · rw [if_pos h] at hs
    exact absurd hs (by decide)
  · exact (not_le.mp h).le

/-- The tail block of the race sums to the survivor part plus the closing
part. -/
theorem tail_sum (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m) (ω : RΩ A BL BR CC κ) :
    ∑ k ∈ Finset.range (max BL.m BR.m + CC.m),
        rsize A BL BR CC κ ε ω (A.m + κ + k)
      = survPart A BL BR CC κ ω + ccPart A BL BR CC κ ω := by
  have hsplit : ∀ k, rsize A BL BR CC κ ε ω (A.m + κ + k)
      = (if 0 < k ∧ k < remCnt A BL BR CC κ ω then
           (if survL A BL BR CC κ ω then
             BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1
            else BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1) else 0)
        + (if remCnt A BL BR CC κ ω < k then
             CC.sizeN (k - remCnt A BL BR CC κ ω) ω.2.2.2.1 else 0) := by
    intro k
    rw [rsize_tail]
    by_cases h0 : k = 0
    · subst h0
      rw [if_pos (Or.inl rfl), if_neg (by omega), if_neg (by omega),
        add_zero]
    · by_cases hR : k = remCnt A BL BR CC κ ω
      · rw [if_pos (Or.inr hR), if_neg (by omega), if_neg (by omega),
          add_zero]
      · rw [if_neg (by omega : ¬(k = 0 ∨ k = remCnt A BL BR CC κ ω))]
        by_cases hlt : k < remCnt A BL BR CC κ ω
        · rw [if_pos hlt,
            if_pos (by omega : 0 < k ∧ k < remCnt A BL BR CC κ ω),
            if_neg (by omega : ¬(remCnt A BL BR CC κ ω < k)), add_zero]
        · rw [if_neg hlt,
            if_neg (by omega : ¬(0 < k ∧ k < remCnt A BL BR CC κ ω)),
            if_pos (by omega : remCnt A BL BR CC κ ω < k), zero_add]
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib]
  rcases Bool.eq_false_or_eq_true (survL A BL BR CC κ ω) with hs | hs
  · have hrem : remCnt A BL BR CC κ ω = BL.m - cntL ω.2.2.2.2 κ := by
      unfold remCnt
      rw [if_pos hs]
    rw [hrem]
    have hterm1 : ∀ k ∈ Finset.range (max BL.m BR.m + CC.m),
        (if 0 < k ∧ k < BL.m - cntL ω.2.2.2.2 κ then
           (if survL A BL BR CC κ ω then
             BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1
            else BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1) else 0)
        = (if 0 < k ∧ k < BL.m - cntL ω.2.2.2.2 κ then
            BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1 else 0) := by
      intro k _
      by_cases hk : 0 < k ∧ k < BL.m - cntL ω.2.2.2.2 κ
      · rw [if_pos hk, if_pos hk, if_pos hs]
      · rw [if_neg hk, if_neg hk]
    rw [Finset.sum_congr rfl hterm1,
      sterm_sum BL ω.2.1
        (le_trans (cntL_le ω.2.2.2.2 (le_refl κ)) hκL)
        (le_trans (Nat.sub_le _ _)
          (le_trans (le_max_left _ _) (Nat.le_add_right _ _))),
      cterm_sum CC ω.2.2.2.1
        (Nat.add_le_add_right
          (le_trans (Nat.sub_le _ _) (le_max_left _ _)) _)]
    unfold survPart ccPart
    rw [if_pos hs]
  · have hrem : remCnt A BL BR CC κ ω = BR.m - cntR ω.2.2.2.2 κ := by
      unfold remCnt
      rw [if_neg (by simp [hs])]
    rw [hrem]
    have hterm1 : ∀ k ∈ Finset.range (max BL.m BR.m + CC.m),
        (if 0 < k ∧ k < BR.m - cntR ω.2.2.2.2 κ then
           (if survL A BL BR CC κ ω then
             BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1
            else BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1) else 0)
        = (if 0 < k ∧ k < BR.m - cntR ω.2.2.2.2 κ then
            BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1 else 0) := by
      intro k _
      by_cases hk : 0 < k ∧ k < BR.m - cntR ω.2.2.2.2 κ
      · rw [if_pos hk, if_pos hk, if_neg (by simp [hs])]
      · rw [if_neg hk, if_neg hk]
    rw [Finset.sum_congr rfl hterm1,
      sterm_sum BR ω.2.2.1
        (le_trans (cntR_le ω.2.2.2.2 (le_refl κ)) hκR)
        (le_trans (Nat.sub_le _ _)
          (le_trans (le_max_right _ _) (Nat.le_add_right _ _))),
      cterm_sum CC ω.2.2.2.1
        (Nat.add_le_add_right
          (le_trans (Nat.sub_le _ _) (le_max_right _ _)) _)]
    unfold survPart ccPart
    rw [if_neg (by simp [hs])]

/-- The pathwise decomposition of the race total. -/
theorem rsum_decomp (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (ω : RΩ A BL BR CC κ) :
    ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω (i : ℕ)
      = preSum A ω.1 A.m
        + (∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
        + survPart A BL BR CC κ ω + ccPart A BL BR CC κ ω := by
  rw [Fin.sum_univ_eq_sum_range,
    show mrace A BL BR CC κ = A.m + κ + (max BL.m BR.m + CC.m) from by
      unfold mrace
      omega,
    sum_range_split (A.m + κ) (max BL.m BR.m + CC.m),
    sum_range_split A.m κ]
  have hA : ∑ i ∈ Finset.range A.m, rsize A BL BR CC κ ε ω i
      = preSum A ω.1 A.m := by
    unfold preSum
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact rsize_A A BL BR CC κ ε ω hi
  have hC : ∑ j ∈ Finset.range κ, rsize A BL BR CC κ ε ω (A.m + j)
      = ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [rsize_coin A BL BR CC κ ε ω hj]
    rfl
  rw [hA, hC, tail_sum A BL BR CC κ ε hκL hκR ω]
  ring

/-- The clamped coin claims differ pathwise by at most `ε`. -/
theorem probL_mul_abs_le {nL nR : ℝ} (hε : 0 < ε) (hL : 0 ≤ nL)
    (hR : 0 ≤ nR) :
    |probL nL nR ε * nL - probL nR nL ε * nR| ≤ ε := by
  unfold probL
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    add_comm (max nR ε) (max nL ε), div_sub_div_same]
  have hDL : ε ≤ max nL ε := le_max_right _ _
  have hDR : ε ≤ max nR ε := le_max_right _ _
  have hD : 0 < max nL ε + max nR ε := by linarith
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  rcases le_total ε nL with h1 | h1 <;> rcases le_total ε nR with h2 | h2
  · rw [max_eq_left h1, max_eq_left h2, mul_comm nR nL, sub_self, abs_zero]
    nlinarith
  · rw [max_eq_left h1, max_eq_right h2, abs_le]
    constructor <;>
      nlinarith [mul_nonneg hL hR, mul_nonneg hε.le hL, sq_nonneg ε,
        mul_le_mul_of_nonneg_left h2 hL]
  · rw [max_eq_right h1, max_eq_left h2, abs_le]
    constructor <;>
      nlinarith [mul_nonneg hL hR, mul_nonneg hε.le hR, sq_nonneg ε,
        mul_le_mul_of_nonneg_left h1 hR]
  · rw [max_eq_right h1, max_eq_right h2, abs_le]
    constructor <;>
      nlinarith [mul_nonneg hL hR, mul_nonneg hε.le hL,
        mul_nonneg hε.le hR, sq_nonneg ε,
        mul_le_mul_of_nonneg_left h1 hε.le,
        mul_le_mul_of_nonneg_left h2 hε.le]

theorem min_eq_avg (x y : ℝ) : min x y = (x + y) / 2 - |x - y| / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith : x - y ≤ 0)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith : 0 ≤ x - y)]
    ring

/-- The coin claim is at least half of the conditionally expected
consumption, up to `ε / 2`. -/
theorem coinTerm_ge (hε : 0 < ε) (ω : RΩ A BL BR CC κ) (j : ℕ) :
    (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
        * nextL A BL BR CC κ ω j
      + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
        * nextR A BL BR CC κ ω j) / 2 - ε / 2
      ≤ coinTerm A BL BR CC κ ε ω j := by
  unfold coinTerm
  rw [min_eq_avg]
  have hL0 : (0 : ℝ) ≤ nextL A BL BR CC κ ω j :=
    BL.sizeN_nonneg (le_refl 0) _ _
  have hR0 : (0 : ℝ) ≤ nextR A BL BR CC κ ω j :=
    BR.sizeN_nonneg (le_refl 0) _ _
  have habs := probL_mul_abs_le ε hε hL0 hR0
  linarith [abs_nonneg (probL (nextL A BL BR CC κ ω j)
    (nextR A BL BR CC κ ω j) ε * nextL A BL BR CC κ ω j
    - probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
      * nextR A BL BR CC κ ω j)]

/-- The survivor part dominates the surviving future mass minus the
consumed minimum and one sacrificed chunk. -/
theorem survPart_ge (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    min (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m)
      - min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω) - cB
      ≤ survPart A BL BR CC κ ω := by
  cases hs : survL A BL BR CC κ ω with
  | true =>
    have hle := (survL_true_iff A BL BR CC κ ω).mp hs
    unfold survPart
    rw [if_pos hs, preSum_succ, ← sumL_eq_preSum κ A BL BR CC ω]
    linarith [min_le_left (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m),
      min_eq_left hle, sizeN_le_cB BL hcB (cntL ω.2.2.2.2 κ) ω.2.1]
  | false =>
    have hle := survL_false_le A BL BR CC κ ω hs
    unfold survPart
    rw [if_neg (by simp [hs]), preSum_succ, ← sumR_eq_preSum κ A BL BR CC ω]
    linarith [min_le_right (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m),
      min_eq_right hle, sizeN_le_cB BR hcB (cntR ω.2.2.2.2 κ) ω.2.2.1]

theorem coinTerm_nonneg (hε : 0 < ε) (ω : RΩ A BL BR CC κ) (j : ℕ) :
    0 ≤ coinTerm A BL BR CC κ ε ω j := by
  unfold coinTerm
  exact le_min
    (mul_nonneg (probL_pos hε).le (BL.sizeN_nonneg (le_refl 0) _ _))
    (mul_nonneg (probL_pos hε).le (BR.sizeN_nonneg (le_refl 0) _ _))

theorem coinTerm_le_cB (hε : 0 < ε) (hcB : 0 ≤ cB)
    (ω : RΩ A BL BR CC κ) (j : ℕ) :
    coinTerm A BL BR CC κ ε ω j ≤ cB := by
  unfold coinTerm
  refine le_trans (min_le_left _ _) (le_trans ?_
    (sizeN_le_cB BL hcB (cntL ω.2.2.2.2 j) ω.2.1))
  exact mul_le_of_le_one_left (BL.sizeN_nonneg (le_refl 0) _ _)
    (probL_lt_one hε).le

theorem survPart_nonneg (ω : RΩ A BL BR CC κ) :
    0 ≤ survPart A BL BR CC κ ω := by
  unfold survPart
  split
  · linarith [preSum_le_total BL ω.2.1 (cntL ω.2.2.2.2 κ + 1)]
  · linarith [preSum_le_total BR ω.2.2.1 (cntR ω.2.2.2.2 κ + 1)]

theorem survPart_le (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    survPart A BL BR CC κ ω ≤ max BL.m BR.m * cB := by
  unfold survPart
  split
  · have h1 := preSum_ub BL ω.2.1 hcB BL.m
    have h2 := preSum_nonneg BL ω.2.1 (cntL ω.2.2.2.2 κ + 1)
    have h3 : (BL.m : ℝ) * cB ≤ max BL.m BR.m * cB := by
      refine mul_le_mul_of_nonneg_right ?_ hcB
      exact_mod_cast Nat.cast_le.mpr (le_max_left _ _)
    linarith
  · have h1 := preSum_ub BR ω.2.2.1 hcB BR.m
    have h2 := preSum_nonneg BR ω.2.2.1 (cntR ω.2.2.2.2 κ + 1)
    have h3 : (BR.m : ℝ) * cB ≤ max BL.m BR.m * cB := by
      refine mul_le_mul_of_nonneg_right ?_ hcB
      exact_mod_cast Nat.cast_le.mpr (le_max_right _ _)
    linarith

theorem ccPart_nonneg (ω : RΩ A BL BR CC κ) :
    0 ≤ ccPart A BL BR CC κ ω := by
  unfold ccPart
  linarith [preSum_le_total CC ω.2.2.2.1 1]

theorem ccPart_le (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    ccPart A BL BR CC κ ω ≤ CC.m * cB := by
  unfold ccPart
  linarith [preSum_ub CC ω.2.2.2.1 hcB CC.m,
    preSum_nonneg CC ω.2.2.2.1 1]

end Pathwise

end Race

end KServer



-- Prove2me | Definitions.Def_KServer_race_hist
-- name    : KServer_race_hist
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T16:02:30.748865+00:00
-- url     : https://prove2.me/theorems/88a06eed-662c-422c-ba23-aa9e1071ca5e
-- title:
--   The race filtration: refinement, adaptedness, and size measurability
-- statement:
--   Fix the setting of the BCR race: four level-$w$ chunk systems $A, B_L, B_R, C$ on a metric space $X$, request transformations into a target space $Y$, $\kappa$ size-weighted coins, and the interleaved race schedule. This file defines the race filtration and proves its three structural properties. The filtration is encoded by a history function with three tags: during the union phase it reveals the history of $A$; during the coin phase after $j$ coins it reveals the full history of $A$, the coin prefix, and the histories of $B_L$ and $B_R$ at their consumption counts; in the tail phase after $k$ steps it reveals the full coin string together with both sides' histories at the coin-determined counts
--   $$\mathrm{rev}_L(k) = \min(\mathrm{cnt}_L(\kappa) + k,\ m_L), \qquad \mathrm{rev}_R(k) = \min(\mathrm{cnt}_R(\kappa) + k,\ m_R),$$
--   and the tail system's history at $\min(k - \mathrm{rem},\ m_C)$, where $\mathrm{rem}$ is the survivor's remaining chunk count. Revealing the dead side at the coin-determined count (rather than freezing it at the kill) is what makes the filtration refining: the revealed counts are functions of the coin string alone, so histories can be compared at equal times through the constituent systems' own refinement properties, while the active system's revealed count still equals exactly its consumption index. The three theorems state: (1) refinement — the time-$j$ atom determines the time-$i$ atom for $i \le j$; (2) adaptedness — the atom at time $r+1$ determines the $r$-th race chunk (including the coin branch, the park sets, the survivor identity, and the tail branches); (3) size measurability — the time-$r$ atom determines the $r$-th race size (using that the two coin-phase systems have trivial time-$0$ history for the first coin's size, and that the phase-transition chunks claim size zero). Hypotheses: $\kappa \le m_L$, $\kappa \le m_R$, and trivial initial histories for $B_L, B_R$. Auxiliary congruence lemmas show that consumed prefixes, park sets, consumed-size sums, the survivor bit, and the remaining count are all determined by the appropriate revealed data.
-- source:
--   Filtration bookkeeping for the race construction in the BCR randomized k-server lower bound, adapted

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace Race

/-! ### The race filtration and its properties

The filtration `rhist2` corrects the tail revelation of `rhist`: in the
tail phase both sides' histories are revealed at the coin-determined
counts `min (cnt κ + k) m` (over-revealing the dead side is harmless for
the cost bounds, by the product structure, while the survivor's count
comes out exactly right), so refinement is provable.  We prove the three
filtration properties of a `ChunkSystemB` for the race: refinement,
adaptedness of the chunks, and measurability of the sizes. -/

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Hist

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- Coin-determined left revelation count in the tail. -/
def revL2 (ω : RΩ A BL BR CC κ) (k : ℕ) : ℕ :=
  min (cntL ω.2.2.2.2 κ + k) BL.m

/-- Coin-determined right revelation count in the tail. -/
def revR2 (ω : RΩ A BL BR CC κ) (k : ℕ) : ℕ :=
  min (cntR ω.2.2.2.2 κ + k) BR.m

open Classical in
/-- The race filtration (coin-determined tail revelation). -/
noncomputable def rhist2 (ω : RΩ A BL BR CC κ) (r : ℕ) : ℕ :=
  if r ≤ A.m then Nat.pair 0 (A.hist r ω.1)
  else if r ≤ A.m + κ then
    Nat.pair 1 (Nat.pair (A.hist A.m ω.1)
      (Nat.pair (coinCode κ ω.2.2.2.2 (r - A.m))
        (Nat.pair (BL.hist (cntL ω.2.2.2.2 (r - A.m)) ω.2.1)
          (BR.hist (cntR ω.2.2.2.2 (r - A.m)) ω.2.2.1))))
  else
    Nat.pair 2 (Nat.pair (A.hist A.m ω.1)
      (Nat.pair (coinCode κ ω.2.2.2.2 κ)
        (Nat.pair (BL.hist (revL2 A BL BR CC κ ω (r - A.m - κ)) ω.2.1)
          (Nat.pair (BR.hist (revR2 A BL BR CC κ ω (r - A.m - κ)) ω.2.2.1)
            (CC.hist (revC A BL BR CC κ ω (r - A.m - κ)) ω.2.2.2.1)))))

theorem rhist2_le_A (ω : RΩ A BL BR CC κ) {r : ℕ} (hr : r ≤ A.m) :
    rhist2 A BL BR CC κ ω r = Nat.pair 0 (A.hist r ω.1) := by
  unfold rhist2
  rw [if_pos hr]

theorem rhist2_coin (ω : RΩ A BL BR CC κ) {r : ℕ} (h1 : A.m < r)
    (h2 : r ≤ A.m + κ) :
    rhist2 A BL BR CC κ ω r
      = Nat.pair 1 (Nat.pair (A.hist A.m ω.1)
          (Nat.pair (coinCode κ ω.2.2.2.2 (r - A.m))
            (Nat.pair (BL.hist (cntL ω.2.2.2.2 (r - A.m)) ω.2.1)
              (BR.hist (cntR ω.2.2.2.2 (r - A.m)) ω.2.2.1)))) := by
  unfold rhist2
  rw [if_neg (by omega), if_pos h2]

theorem rhist2_tail (ω : RΩ A BL BR CC κ) {r : ℕ} (h1 : A.m + κ < r) :
    rhist2 A BL BR CC κ ω r
      = Nat.pair 2 (Nat.pair (A.hist A.m ω.1)
          (Nat.pair (coinCode κ ω.2.2.2.2 κ)
            (Nat.pair (BL.hist (revL2 A BL BR CC κ ω (r - A.m - κ)) ω.2.1)
              (Nat.pair
                (BR.hist (revR2 A BL BR CC κ ω (r - A.m - κ)) ω.2.2.1)
                (CC.hist (revC A BL BR CC κ ω (r - A.m - κ))
                  ω.2.2.2.1))))) := by
  unfold rhist2
  rw [if_neg (by omega), if_neg (by omega)]

end Hist


section Congr

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- Sizes below a revealed count are determined. -/
theorem sizeN_congr_le (C : ChunkSystemB X s t 0 cB T pe mL) {n N : ℕ}
    (hn : n ≤ N) {ωa ωb : C.Ω} (h : C.hist N ωa = C.hist N ωb) :
    C.sizeN n ωa = C.sizeN n ωb :=
  C.sizeN_congr (C.href n N hn _ _ h)

/-- Chunks strictly below a revealed count are determined. -/
theorem chunkN_congr (C : ChunkSystemB X s t 0 cB T pe mL) {n N : ℕ}
    (hn : n + 1 ≤ N) {ωa ωb : C.Ω} (h : C.hist N ωa = C.hist N ωb) :
    chunkN C ωa n = chunkN C ωb n := by
  unfold chunkN
  by_cases hm : n < C.m
  · rw [dif_pos hm, dif_pos hm]
    exact C.hadapt ⟨n, hm⟩ _ _ (C.href (n + 1) N hn _ _ h)
  · rw [dif_neg hm, dif_neg hm]

/-- The consumed prefix below a revealed count is determined. -/
theorem take_congr (C : ChunkSystemB X s t 0 cB T pe mL) {n N : ℕ}
    (hn : n ≤ N) {ωa ωb : C.Ω} (h : C.hist N ωa = C.hist N ωb) :
    (List.ofFn (C.chunk ωa)).take n = (List.ofFn (C.chunk ωb)).take n := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_take, List.length_ofFn,
      List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_take, List.getElem_take, List.getElem_ofFn,
      List.getElem_ofFn]
    have hi : i < C.m := by
      rw [List.length_take, List.length_ofFn] at h1
      omega
    have hin : i < n := by
      rw [List.length_take, List.length_ofFn] at h1
      omega
    exact C.hadapt ⟨i, hi⟩ _ _ (C.href (i + 1) N (by omega) _ _ h)

theorem lastXset_congr (C : ChunkSystemB X s t 0 cB T pe mL) {n N : ℕ}
    (hn : n ≤ N) {ωa ωb : C.Ω} (h : C.hist N ωa = C.hist N ωb) :
    lastXset C ωa n = lastXset C ωb n := by
  unfold lastXset
  rw [take_congr C hn h]

theorem sumL_congr {ω ω' : RΩ A BL BR CC κ}
    (hc : ω.2.2.2.2 = ω'.2.2.2.2) {N : ℕ} (hN : cntL ω.2.2.2.2 κ ≤ N)
    (hL : BL.hist N ω.2.1 = BL.hist N ω'.2.1) :
    sumL A BL BR CC κ ω = sumL A BL BR CC κ ω' := by
  unfold sumL nextL
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hc]
  by_cases hb : ω.2.2.2.2 j
  · rw [if_pos hb, if_pos hb]
    exact sizeN_congr_le BL
      (le_trans (cntL_mono _ (le_of_lt j.isLt)) hN) hL
  · rw [if_neg hb, if_neg hb]

theorem sumR_congr {ω ω' : RΩ A BL BR CC κ}
    (hc : ω.2.2.2.2 = ω'.2.2.2.2) {N : ℕ} (hN : cntR ω.2.2.2.2 κ ≤ N)
    (hR : BR.hist N ω.2.2.1 = BR.hist N ω'.2.2.1) :
    sumR A BL BR CC κ ω = sumR A BL BR CC κ ω' := by
  unfold sumR nextR
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hc]
  by_cases hb : ω.2.2.2.2 j
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb]
    exact sizeN_congr_le BR
      (le_trans (cntR_mono _ (le_of_lt j.isLt)) hN) hR

theorem survL_congr {ω ω' : RΩ A BL BR CC κ}
    (hc : ω.2.2.2.2 = ω'.2.2.2.2)
    {NL NR : ℕ} (hNL : cntL ω.2.2.2.2 κ ≤ NL)
    (hNR : cntR ω.2.2.2.2 κ ≤ NR)
    (hL : BL.hist NL ω.2.1 = BL.hist NL ω'.2.1)
    (hR : BR.hist NR ω.2.2.1 = BR.hist NR ω'.2.2.1) :
    survL A BL BR CC κ ω = survL A BL BR CC κ ω' := by
  unfold survL
  rw [sumL_congr A BL BR CC κ hc hNL hL, sumR_congr A BL BR CC κ hc hNR hR]

theorem remCnt_congr {ω ω' : RΩ A BL BR CC κ}
    (hc : ω.2.2.2.2 = ω'.2.2.2.2)
    {NL NR : ℕ} (hNL : cntL ω.2.2.2.2 κ ≤ NL)
    (hNR : cntR ω.2.2.2.2 κ ≤ NR)
    (hL : BL.hist NL ω.2.1 = BL.hist NL ω'.2.1)
    (hR : BR.hist NR ω.2.2.1 = BR.hist NR ω'.2.2.1) :
    remCnt A BL BR CC κ ω = remCnt A BL BR CC κ ω' := by
  unfold remCnt
  rw [survL_congr A BL BR CC κ hc hNL hNR hL hR, hc]

theorem revC_congr {ω ω' : RΩ A BL BR CC κ}
    (hc : ω.2.2.2.2 = ω'.2.2.2.2)
    {NL NR : ℕ} (hNL : cntL ω.2.2.2.2 κ ≤ NL)
    (hNR : cntR ω.2.2.2.2 κ ≤ NR)
    (hL : BL.hist NL ω.2.1 = BL.hist NL ω'.2.1)
    (hR : BR.hist NR ω.2.2.1 = BR.hist NR ω'.2.2.1) (k : ℕ) :
    revC A BL BR CC κ ω k = revC A BL BR CC κ ω' k := by
  unfold revC
  rw [remCnt_congr A BL BR CC κ hc hNL hNR hL hR]

end Congr


section Main

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- Refinement of the race filtration. -/
theorem rhist2_refine (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {i j : ℕ} (hij : i ≤ j) (ω ω' : RΩ A BL BR CC κ)
    (h : rhist2 A BL BR CC κ ω j = rhist2 A BL BR CC κ ω' j) :
    rhist2 A BL BR CC κ ω i = rhist2 A BL BR CC κ ω' i := by
  by_cases hj1 : j ≤ A.m
  · rw [rhist2_le_A A BL BR CC κ ω hj1, rhist2_le_A A BL BR CC κ ω' hj1,
      Nat.pair_eq_pair] at h
    rw [rhist2_le_A A BL BR CC κ ω (le_trans hij hj1),
      rhist2_le_A A BL BR CC κ ω' (le_trans hij hj1),
      A.href i j hij _ _ h.2]
  · rw [not_le] at hj1
    by_cases hj2 : j ≤ A.m + κ
    · -- tag 1 at `j`
      rw [rhist2_coin A BL BR CC κ ω hj1 hj2,
        rhist2_coin A BL BR CC κ ω' hj1 hj2] at h
      simp only [Nat.pair_eq_pair] at h
      obtain ⟨-, hA, hcode, hL, hR⟩ := h
      have hcs : ∀ ii : Fin κ, (ii : ℕ) < j - A.m →
          ω.2.2.2.2 ii = ω'.2.2.2.2 ii := coinCode_inj hcode
      have hcntL : cntL ω'.2.2.2.2 (j - A.m) = cntL ω.2.2.2.2 (j - A.m) :=
        (cntL_congr hcs).symm
      have hcntR : cntR ω'.2.2.2.2 (j - A.m) = cntR ω.2.2.2.2 (j - A.m) :=
        (cntR_congr hcs).symm
      rw [hcntL] at hL
      rw [hcntR] at hR
      by_cases hi1 : i ≤ A.m
      · rw [rhist2_le_A A BL BR CC κ ω hi1,
          rhist2_le_A A BL BR CC κ ω' hi1, A.href i A.m hi1 _ _ hA]
      · rw [not_le] at hi1
        have hi2 : i ≤ A.m + κ := le_trans hij hj2
        rw [rhist2_coin A BL BR CC κ ω hi1 hi2,
          rhist2_coin A BL BR CC κ ω' hi1 hi2]
        have hcsi : ∀ ii : Fin κ, (ii : ℕ) < i - A.m →
            ω.2.2.2.2 ii = ω'.2.2.2.2 ii := fun ii hii => hcs ii (by omega)
        have hLi : BL.hist (cntL ω.2.2.2.2 (i - A.m)) ω.2.1
            = BL.hist (cntL ω'.2.2.2.2 (i - A.m)) ω'.2.1 := by
          rw [show cntL ω'.2.2.2.2 (i - A.m) = cntL ω.2.2.2.2 (i - A.m)
            from (cntL_congr hcsi).symm]
          exact BL.href _ _ (cntL_mono _ (by omega)) _ _ hL
        have hRi : BR.hist (cntR ω.2.2.2.2 (i - A.m)) ω.2.2.1
            = BR.hist (cntR ω'.2.2.2.2 (i - A.m)) ω'.2.2.1 := by
          rw [show cntR ω'.2.2.2.2 (i - A.m) = cntR ω.2.2.2.2 (i - A.m)
            from (cntR_congr hcsi).symm]
          exact BR.href _ _ (cntR_mono _ (by omega)) _ _ hR
        rw [hLi, hRi, hA, coinCode_congr hcsi]
    · -- tag 2 at `j`
      rw [not_le] at hj2
      rw [rhist2_tail A BL BR CC κ ω hj2,
        rhist2_tail A BL BR CC κ ω' hj2] at h
      simp only [Nat.pair_eq_pair] at h
      obtain ⟨-, hA, hcode, hL, hR, hC⟩ := h
      have hceq : ω.2.2.2.2 = ω'.2.2.2.2 :=
        funext fun ii => coinCode_inj hcode ii ii.isLt
      have hrevL : ∀ kk, revL2 A BL BR CC κ ω' kk
          = revL2 A BL BR CC κ ω kk := by
        intro kk; unfold revL2; rw [hceq]
      have hrevR : ∀ kk, revR2 A BL BR CC κ ω' kk
          = revR2 A BL BR CC κ ω kk := by
        intro kk; unfold revR2; rw [hceq]
      rw [hrevL] at hL
      rw [hrevR] at hR
      have hNL : cntL ω.2.2.2.2 κ ≤ revL2 A BL BR CC κ ω (j - A.m - κ) := by
        unfold revL2
        exact le_min (Nat.le_add_right _ _)
          (le_trans (cntL_le _ le_rfl) hκL)
      have hNR : cntR ω.2.2.2.2 κ ≤ revR2 A BL BR CC κ ω (j - A.m - κ) := by
        unfold revR2
        exact le_min (Nat.le_add_right _ _)
          (le_trans (cntR_le _ le_rfl) hκR)
      have hCk : revC A BL BR CC κ ω' (j - A.m - κ)
          = revC A BL BR CC κ ω (j - A.m - κ) :=
        (revC_congr A BL BR CC κ hceq hNL hNR hL hR _).symm
      rw [hCk] at hC
      by_cases hi1 : i ≤ A.m
      · rw [rhist2_le_A A BL BR CC κ ω hi1,
          rhist2_le_A A BL BR CC κ ω' hi1, A.href i A.m hi1 _ _ hA]
      · rw [not_le] at hi1
        by_cases hi2 : i ≤ A.m + κ
        · rw [rhist2_coin A BL BR CC κ ω hi1 hi2,
            rhist2_coin A BL BR CC κ ω' hi1 hi2]
          have hLi : BL.hist (cntL ω.2.2.2.2 (i - A.m)) ω.2.1
              = BL.hist (cntL ω'.2.2.2.2 (i - A.m)) ω'.2.1 := by
            rw [show cntL ω'.2.2.2.2 (i - A.m) = cntL ω.2.2.2.2 (i - A.m)
              from by rw [hceq]]
            exact BL.href _ _
              (le_trans (cntL_mono _ (by omega : i - A.m ≤ κ)) hNL) _ _ hL
          have hRi : BR.hist (cntR ω.2.2.2.2 (i - A.m)) ω.2.2.1
              = BR.hist (cntR ω'.2.2.2.2 (i - A.m)) ω'.2.2.1 := by
            rw [show cntR ω'.2.2.2.2 (i - A.m) = cntR ω.2.2.2.2 (i - A.m)
              from by rw [hceq]]
            exact BR.href _ _
              (le_trans (cntR_mono _ (by omega : i - A.m ≤ κ)) hNR) _ _ hR
          rw [hLi, hRi, hA, show coinCode κ ω.2.2.2.2 (i - A.m)
            = coinCode κ ω'.2.2.2.2 (i - A.m) from by rw [hceq]]
        · rw [not_le] at hi2
          rw [rhist2_tail A BL BR CC κ ω hi2,
            rhist2_tail A BL BR CC κ ω' hi2]
          have hki : i - A.m - κ ≤ j - A.m - κ := by omega
          have hLi : BL.hist (revL2 A BL BR CC κ ω (i - A.m - κ)) ω.2.1
              = BL.hist (revL2 A BL BR CC κ ω' (i - A.m - κ)) ω'.2.1 := by
            rw [hrevL]
            refine BL.href _ _ ?_ _ _ hL
            unfold revL2
            exact min_le_min (by omega) le_rfl
          have hRi : BR.hist (revR2 A BL BR CC κ ω (i - A.m - κ)) ω.2.2.1
              = BR.hist (revR2 A BL BR CC κ ω' (i - A.m - κ)) ω'.2.2.1 := by
            rw [hrevR]
            refine BR.href _ _ ?_ _ _ hR
            unfold revR2
            exact min_le_min (by omega) le_rfl
          have hCi : CC.hist (revC A BL BR CC κ ω (i - A.m - κ)) ω.2.2.2.1
              = CC.hist (revC A BL BR CC κ ω' (i - A.m - κ)) ω'.2.2.2.1 := by
            rw [show revC A BL BR CC κ ω' (i - A.m - κ)
                = revC A BL BR CC κ ω (i - A.m - κ)
              from (revC_congr A BL BR CC κ hceq hNL hNR hL hR _).symm]
            refine CC.href _ _ ?_ _ _ hC
            unfold revC
            exact min_le_min (Nat.sub_le_sub_right hki _) le_rfl
          rw [hLi, hRi, hCi, hA, show coinCode κ ω.2.2.2.2 κ
            = coinCode κ ω'.2.2.2.2 κ from by rw [hceq]]

/-- Adaptedness of the race chunks to the race filtration. -/
theorem rchunk_adapt (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {r : ℕ} (ω ω' : RΩ A BL BR CC κ)
    (h : rhist2 A BL BR CC κ ω (r + 1) = rhist2 A BL BR CC κ ω' (r + 1)) :
    rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
      = rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω' r := by
  by_cases hr1 : r < A.m
  · rw [rhist2_le_A A BL BR CC κ ω (by omega),
      rhist2_le_A A BL BR CC κ ω' (by omega), Nat.pair_eq_pair] at h
    rw [rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hr1,
      rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω' hr1,
      chunkN_congr A (le_refl (r + 1)) h.2]
  · rw [not_lt] at hr1
    by_cases hr2 : r < A.m + κ
    · -- coin chunk
      obtain ⟨j, rfl⟩ : ∃ j, r = A.m + j := ⟨r - A.m, by omega⟩
      have hj : j < κ := by omega
      rw [rhist2_coin A BL BR CC κ ω (by omega) (by omega),
        rhist2_coin A BL BR CC κ ω' (by omega) (by omega)] at h
      simp only [Nat.pair_eq_pair,
        show A.m + j + 1 - A.m = j + 1 from by omega] at h
      obtain ⟨-, hA, hcode, hL, hR⟩ := h
      have hcs : ∀ ii : Fin κ, (ii : ℕ) < j + 1 →
          ω.2.2.2.2 ii = ω'.2.2.2.2 ii := coinCode_inj hcode
      have hcs' : ∀ ii : Fin κ, (ii : ℕ) < j →
          ω.2.2.2.2 ii = ω'.2.2.2.2 ii := fun ii hii => hcs ii (by omega)
      have hcntL1 : cntL ω'.2.2.2.2 (j + 1) = cntL ω.2.2.2.2 (j + 1) :=
        (cntL_congr hcs).symm
      have hcntR1 : cntR ω'.2.2.2.2 (j + 1) = cntR ω.2.2.2.2 (j + 1) :=
        (cntR_congr hcs).symm
      rw [hcntL1] at hL
      rw [hcntR1] at hR
      have hcntL : cntL ω'.2.2.2.2 j = cntL ω.2.2.2.2 j :=
        (cntL_congr hcs').symm
      have hcntR : cntR ω'.2.2.2.2 j = cntR ω.2.2.2.2 j :=
        (cntR_congr hcs').symm
      rw [rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj,
        rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω' hj]
      have hbj : ω'.2.2.2.2 ⟨j, hj⟩ = ω.2.2.2.2 ⟨j, hj⟩ :=
        (hcs ⟨j, hj⟩ (Nat.lt_succ_self j)).symm
      have hparkR : parkR A BL BR CC GmR κ ω j
          = parkR A BL BR CC GmR κ ω' j := by
        unfold parkR
        rw [hcntR, lastXset_congr BR (cntR_mono _ (Nat.le_succ j)) hR]
      have hparkL : parkL A BL BR CC GmL κ ω j
          = parkL A BL BR CC GmL κ ω' j := by
        unfold parkL
        rw [hcntL, lastXset_congr BL (cntL_mono _ (Nat.le_succ j)) hL]
      rw [hbj, hcntL, hcntR]
      by_cases hb : ω.2.2.2.2 ⟨j, hj⟩
      · rw [if_pos hb, if_pos hb]
        have hstep : cntL ω.2.2.2.2 (j + 1) = cntL ω.2.2.2.2 j + 1 := by
          rw [cntL_succ _ hj, if_pos hb]
        rw [hparkR, chunkN_congr BL (le_of_eq hstep.symm) hL]
      · rw [if_neg hb, if_neg hb]
        have hstep : cntR ω.2.2.2.2 (j + 1) = cntR ω.2.2.2.2 j + 1 := by
          rw [cntR_succ _ hj, if_pos (by simpa using hb)]
        rw [hparkL, chunkN_congr BR (le_of_eq hstep.symm) hR]
    · -- tail chunk
      rw [not_lt] at hr2
      obtain ⟨k, rfl⟩ : ∃ k, r = A.m + κ + k := ⟨r - A.m - κ, by omega⟩
      rw [rhist2_tail A BL BR CC κ ω (by omega),
        rhist2_tail A BL BR CC κ ω' (by omega)] at h
      simp only [Nat.pair_eq_pair,
        show A.m + κ + k + 1 - A.m - κ = k + 1 from by omega] at h
      obtain ⟨-, hA, hcode, hL, hR, hC⟩ := h
      have hceq : ω.2.2.2.2 = ω'.2.2.2.2 :=
        funext fun ii => coinCode_inj hcode ii ii.isLt
      have hrevL : ∀ kk, revL2 A BL BR CC κ ω' kk
          = revL2 A BL BR CC κ ω kk := by
        intro kk; unfold revL2; rw [hceq]
      have hrevR : ∀ kk, revR2 A BL BR CC κ ω' kk
          = revR2 A BL BR CC κ ω kk := by
        intro kk; unfold revR2; rw [hceq]
      rw [hrevL] at hL
      rw [hrevR] at hR
      have hcmL : cntL ω.2.2.2.2 κ ≤ BL.m :=
        le_trans (cntL_le _ le_rfl) hκL
      have hcmR : cntR ω.2.2.2.2 κ ≤ BR.m :=
        le_trans (cntR_le _ le_rfl) hκR
      have hNL : cntL ω.2.2.2.2 κ ≤ revL2 A BL BR CC κ ω (k + 1) := by
        unfold revL2; omega
      have hNR : cntR ω.2.2.2.2 κ ≤ revR2 A BL BR CC κ ω (k + 1) := by
        unfold revR2; omega
      have hsurv := survL_congr A BL BR CC κ hceq hNL hNR hL hR
      have hrem := remCnt_congr A BL BR CC κ hceq hNL hNR hL hR
      have hCk : revC A BL BR CC κ ω' (k + 1)
          = revC A BL BR CC κ ω (k + 1) :=
        (revC_congr A BL BR CC κ hceq hNL hNR hL hR _).symm
      rw [hCk] at hC
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω' k,
        ← hsurv, ← hrem, ← hceq]
      by_cases hs : survL A BL BR CC κ ω
      · rw [if_pos hs, if_pos hs]
        have hremv : remCnt A BL BR CC κ ω = BL.m - cntL ω.2.2.2.2 κ := by
          unfold remCnt; rw [if_pos hs]
        by_cases hk : k < remCnt A BL BR CC κ ω
        · rw [if_pos hk, if_pos hk]
          have hidx : cntL ω.2.2.2.2 κ + k + 1
              ≤ revL2 A BL BR CC κ ω (k + 1) := by
            unfold revL2; omega
          rw [chunkN_congr BL hidx hL]
        · rw [if_neg hk, if_neg hk]
          by_cases hk2 : k - remCnt A BL BR CC κ ω < CC.m
          · rw [if_pos hk2, if_pos hk2]
            have hidx : (k - remCnt A BL BR CC κ ω) + 1
                ≤ revC A BL BR CC κ ω (k + 1) := by
              unfold revC; omega
            rw [chunkN_congr CC hidx hC]
          · rw [if_neg hk2, if_neg hk2]
      · rw [if_neg hs, if_neg hs]
        have hremv : remCnt A BL BR CC κ ω = BR.m - cntR ω.2.2.2.2 κ := by
          unfold remCnt; rw [if_neg hs]
        by_cases hk : k < remCnt A BL BR CC κ ω
        · rw [if_pos hk, if_pos hk]
          have hidx : cntR ω.2.2.2.2 κ + k + 1
              ≤ revR2 A BL BR CC κ ω (k + 1) := by
            unfold revR2; omega
          rw [chunkN_congr BR hidx hR]
        · rw [if_neg hk, if_neg hk]
          by_cases hk2 : k - remCnt A BL BR CC κ ω < CC.m
          · rw [if_pos hk2, if_pos hk2]
            have hidx : (k - remCnt A BL BR CC κ ω) + 1
                ≤ revC A BL BR CC κ ω (k + 1) := by
              unfold revC; omega
            rw [chunkN_congr CC hidx hC]
          · rw [if_neg hk2, if_neg hk2]

/-- Measurability of the race sizes with respect to the race filtration. -/
theorem rsize_smeas (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (h0L : ∀ ωa ωb : BL.Ω, BL.hist 0 ωa = BL.hist 0 ωb)
    (h0R : ∀ ωa ωb : BR.Ω, BR.hist 0 ωa = BR.hist 0 ωb)
    {r : ℕ} (ω ω' : RΩ A BL BR CC κ)
    (h : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω' r) :
    rsize A BL BR CC κ ε ω r = rsize A BL BR CC κ ε ω' r := by
  by_cases hr1 : r < A.m
  · rw [rhist2_le_A A BL BR CC κ ω (by omega),
      rhist2_le_A A BL BR CC κ ω' (by omega), Nat.pair_eq_pair] at h
    rw [rsize_A A BL BR CC κ ε ω hr1, rsize_A A BL BR CC κ ε ω' hr1]
    exact A.sizeN_congr h.2
  · rw [not_lt] at hr1
    by_cases hr2 : r < A.m + κ
    · -- coin size
      obtain ⟨j, rfl⟩ : ∃ j, r = A.m + j := ⟨r - A.m, by omega⟩
      have hj : j < κ := by omega
      rw [rsize_coin A BL BR CC κ ε ω hj, rsize_coin A BL BR CC κ ε ω' hj]
      by_cases hj0 : j = 0
      · subst hj0
        have hnL : nextL A BL BR CC κ ω 0 = nextL A BL BR CC κ ω' 0 := by
          unfold nextL
          rw [cntL_zero, cntL_zero]
          exact BL.sizeN_congr (h0L _ _)
        have hnR : nextR A BL BR CC κ ω 0 = nextR A BL BR CC κ ω' 0 := by
          unfold nextR
          rw [cntR_zero, cntR_zero]
          exact BR.sizeN_congr (h0R _ _)
        rw [hnL, hnR]
      · rw [rhist2_coin A BL BR CC κ ω (by omega) (by omega),
          rhist2_coin A BL BR CC κ ω' (by omega) (by omega)] at h
        simp only [Nat.pair_eq_pair, Nat.add_sub_cancel_left] at h
        obtain ⟨-, hA, hcode, hL, hR⟩ := h
        have hcs : ∀ ii : Fin κ, (ii : ℕ) < j →
            ω.2.2.2.2 ii = ω'.2.2.2.2 ii := coinCode_inj hcode
        have hcntL : cntL ω'.2.2.2.2 j = cntL ω.2.2.2.2 j :=
          (cntL_congr hcs).symm
        have hcntR : cntR ω'.2.2.2.2 j = cntR ω.2.2.2.2 j :=
          (cntR_congr hcs).symm
        rw [hcntL] at hL
        rw [hcntR] at hR
        have hnL : nextL A BL BR CC κ ω j = nextL A BL BR CC κ ω' j := by
          unfold nextL
          rw [hcntL]
          exact BL.sizeN_congr hL
        have hnR : nextR A BL BR CC κ ω j = nextR A BL BR CC κ ω' j := by
          unfold nextR
          rw [hcntR]
          exact BR.sizeN_congr hR
        rw [hnL, hnR]
    · -- tail size
      rw [not_lt] at hr2
      obtain ⟨k, rfl⟩ : ∃ k, r = A.m + κ + k := ⟨r - A.m - κ, by omega⟩
      rw [rsize_tail A BL BR CC κ ε ω k, rsize_tail A BL BR CC κ ε ω' k]
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos (Or.inl rfl), if_pos (Or.inl rfl)]
      · rw [rhist2_tail A BL BR CC κ ω (by omega),
          rhist2_tail A BL BR CC κ ω' (by omega)] at h
        simp only [Nat.pair_eq_pair,
          show A.m + κ + k - A.m - κ = k from by omega] at h
        obtain ⟨-, hA, hcode, hL, hR, hC⟩ := h
        have hceq : ω.2.2.2.2 = ω'.2.2.2.2 :=
          funext fun ii => coinCode_inj hcode ii ii.isLt
        have hrevL : ∀ kk, revL2 A BL BR CC κ ω' kk
            = revL2 A BL BR CC κ ω kk := by
          intro kk; unfold revL2; rw [hceq]
        have hrevR : ∀ kk, revR2 A BL BR CC κ ω' kk
            = revR2 A BL BR CC κ ω kk := by
          intro kk; unfold revR2; rw [hceq]
        rw [hrevL] at hL
        rw [hrevR] at hR
        have hcmL : cntL ω.2.2.2.2 κ ≤ BL.m :=
          le_trans (cntL_le _ le_rfl) hκL
        have hcmR : cntR ω.2.2.2.2 κ ≤ BR.m :=
          le_trans (cntR_le _ le_rfl) hκR
        have hNL : cntL ω.2.2.2.2 κ ≤ revL2 A BL BR CC κ ω k := by
          unfold revL2; omega
        have hNR : cntR ω.2.2.2.2 κ ≤ revR2 A BL BR CC κ ω k := by
          unfold revR2; omega
        have hsurv := survL_congr A BL BR CC κ hceq hNL hNR hL hR
        have hrem := remCnt_congr A BL BR CC κ hceq hNL hNR hL hR
        have hCk : revC A BL BR CC κ ω' k = revC A BL BR CC κ ω k :=
          (revC_congr A BL BR CC κ hceq hNL hNR hL hR _).symm
        rw [hCk] at hC
        rw [← hsurv, ← hrem, ← hceq]
        by_cases hke : k = remCnt A BL BR CC κ ω
        · rw [if_pos (Or.inr hke), if_pos (Or.inr hke)]
        · have hne : ¬(k = 0 ∨ k = remCnt A BL BR CC κ ω) := by
            push_neg
            exact ⟨hk0, hke⟩
          rw [if_neg hne, if_neg hne]
          by_cases hk : k < remCnt A BL BR CC κ ω
          · rw [if_pos hk, if_pos hk]
            by_cases hs : survL A BL BR CC κ ω
            · rw [if_pos hs, if_pos hs]
              have hremv : remCnt A BL BR CC κ ω
                  = BL.m - cntL ω.2.2.2.2 κ := by
                unfold remCnt; rw [if_pos hs]
              have hidx : revL2 A BL BR CC κ ω k
                  = cntL ω.2.2.2.2 κ + k := by
                unfold revL2; omega
              refine BL.sizeN_congr ?_
              rw [← hidx]
              exact hL
            · rw [if_neg hs, if_neg hs]
              have hremv : remCnt A BL BR CC κ ω
                  = BR.m - cntR ω.2.2.2.2 κ := by
                unfold remCnt; rw [if_neg hs]
              have hidx : revR2 A BL BR CC κ ω k
                  = cntR ω.2.2.2.2 κ + k := by
                unfold revR2; omega
              refine BR.sizeN_congr ?_
              rw [← hidx]
              exact hR
          · rw [if_neg hk, if_neg hk]
            by_cases hn : k - remCnt A BL BR CC κ ω < CC.m
            · have hidx : revC A BL BR CC κ ω k
                  = k - remCnt A BL BR CC κ ω := by
                unfold revC; omega
              refine CC.sizeN_congr ?_
              rw [← hidx]
              exact hC
            · rw [not_lt] at hn
              unfold ChunkSystemB.sizeN
              rw [dif_neg (by omega), dif_neg (by omega)]

end Main


end Race

end KServer



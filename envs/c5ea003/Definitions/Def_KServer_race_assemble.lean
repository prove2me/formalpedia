-- Prove2me | Definitions.Def_KServer_race_assemble
-- name    : KServer_race_assemble
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T17:55:54.251035+00:00
-- url     : https://prove2.me/theorems/46d63b35-4cec-41fb-972f-7669ebeea6b6
-- title:
--   The race as a chunk system: the full assembly
-- statement:
--   The main assembly of the BCR race: four constituent chunk systems $A, B_L, B_R, C$ on $X$ (entry $s$, exit $t$, sizes in $[0, c_B]$, price $p_e$, no empty chunks, trivial initial histories), together with the coin race and the geometric package — retractions $\pi$ and nonexpansive lifts $\iota$ for each of the five request transformations, junction equations, the pinned tail images $G_{TL}\{t\} = G_{TR}\{t\} = \{\mathrm{stop}\}$, the separation/dichotomy data ($\mathrm{sep} \ge \mathrm{diam}(X) + p_e$, left/right image separation, and the side dichotomy for evader positions), and $3\,d(s,t) \le d(\iota_A(s), \mathrm{stop})$ — produce a chunk system with online escapes on the target space $Y$:
--   $$\mathrm{Race}(A, B_L, B_R, C) \;:\; \mathrm{ChunkSystemB}\bigl(Y,\ \iota_A(s),\ \mathrm{stop},\ [0, c_B],\ T_{\mathrm{race}},\ p',\ m_{\mathrm{race}}\bigr),$$
--   carrying the trivial-initial-history, variance, and no-empty-chunk conjuncts. The expected-total bound $T_{\mathrm{race}}$ and the variance bound enter as hypotheses on the race totals, to be established separately by the martingale analysis of the coin phase. All structural fields are discharged by the previously published race components: positivity and normalization of the product measure with the size-weighted coin tree, refinement/adaptedness/measurability of the corrected filtration, nonemptiness, the pinned ending, the follow-the-survivor offline bound, the size bounds, and the all-phase chunk-cost bound. This file also proves the auxiliary size bounds ($0 \le \mathrm{size} \le c_B$, using that the coin claims are dominated by one side's next size) and that every race chunk is a nonempty list.
-- source:
--   Assembly of the race construction in the BCR randomized k-server lower bound, adapted

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

section Assemble

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- Size bounds for the race. -/
theorem rsize_bounds (hε : 0 < ε) (hcB : 0 ≤ cB)
    (ω : RΩ A BL BR CC κ) (r : ℕ) :
    0 ≤ rsize A BL BR CC κ ε ω r ∧ rsize A BL BR CC κ ε ω r ≤ cB := by
  by_cases hr1 : r < A.m
  · rw [rsize_A A BL BR CC κ ε ω hr1]
    constructor
    · exact A.sizeN_nonneg (le_refl 0) r ω.1
    · by_cases hm : r < A.m
      · unfold ChunkSystemB.sizeN
        rw [dif_pos hm]
        exact (A.hsize ω.1 ⟨r, hm⟩).2
      · unfold ChunkSystemB.sizeN
        rw [dif_neg hm]
        exact hcB
  · rw [not_lt] at hr1
    by_cases hr2 : r < A.m + κ
    · obtain ⟨j, rfl⟩ : ∃ j, r = A.m + j := ⟨r - A.m, by omega⟩
      have hj : j < κ := by omega
      rw [rsize_coin A BL BR CC κ ε ω hj]
      have hnL0 : 0 ≤ nextL A BL BR CC κ ω j :=
        BL.sizeN_nonneg (le_refl 0) _ _
      have hnR0 : 0 ≤ nextR A BL BR CC κ ω j :=
        BR.sizeN_nonneg (le_refl 0) _ _
      have hpL := probL_pos (nL := nextL A BL BR CC κ ω j)
        (nR := nextR A BL BR CC κ ω j) hε
      have hpL1 := probL_lt_one (nL := nextL A BL BR CC κ ω j)
        (nR := nextR A BL BR CC κ ω j) hε
      have hpR := probL_pos (nL := nextR A BL BR CC κ ω j)
        (nR := nextL A BL BR CC κ ω j) hε
      have hpR1 := probL_lt_one (nL := nextR A BL BR CC κ ω j)
        (nR := nextL A BL BR CC κ ω j) hε
      constructor
      · refine le_min ?_ ?_
        · exact mul_nonneg (le_of_lt hpL) hnL0
        · exact mul_nonneg (le_of_lt hpR) hnR0
      · refine le_trans (min_le_left _ _) ?_
        have h1 : probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
            * nextL A BL BR CC κ ω j ≤ 1 * nextL A BL BR CC κ ω j :=
          mul_le_mul_of_nonneg_right (le_of_lt hpL1) hnL0
        rw [one_mul] at h1
        refine le_trans h1 ?_
        unfold nextL ChunkSystemB.sizeN
        by_cases hm : cntL ω.2.2.2.2 j < BL.m
        · rw [dif_pos hm]
          exact (BL.hsize ω.2.1 _).2
        · rw [dif_neg hm]
          exact hcB
    · rw [not_lt] at hr2
      obtain ⟨k, rfl⟩ : ∃ k, r = A.m + κ + k := ⟨r - A.m - κ, by omega⟩
      rw [rsize_tail A BL BR CC κ ε ω k]
      by_cases hz : k = 0 ∨ k = remCnt A BL BR CC κ ω
      · rw [if_pos hz]
        exact ⟨le_refl 0, hcB⟩
      · rw [if_neg hz]
        by_cases hk : k < remCnt A BL BR CC κ ω
        · rw [if_pos hk]
          by_cases hs : survL A BL BR CC κ ω
          · rw [if_pos hs]
            constructor
            · exact BL.sizeN_nonneg (le_refl 0) _ _
            · unfold ChunkSystemB.sizeN
              by_cases hm : cntL ω.2.2.2.2 κ + k < BL.m
              · rw [dif_pos hm]
                exact (BL.hsize ω.2.1 _).2
              · rw [dif_neg hm]
                exact hcB
          · rw [if_neg hs]
            constructor
            · exact BR.sizeN_nonneg (le_refl 0) _ _
            · unfold ChunkSystemB.sizeN
              by_cases hm : cntR ω.2.2.2.2 κ + k < BR.m
              · rw [dif_pos hm]
                exact (BR.hsize ω.2.2.1 _).2
              · rw [dif_neg hm]
                exact hcB
        · rw [if_neg hk]
          constructor
          · exact CC.sizeN_nonneg (le_refl 0) _ _
          · unfold ChunkSystemB.sizeN
            by_cases hm : k - remCnt A BL BR CC κ ω < CC.m
            · rw [dif_pos hm]
              exact (CC.hsize ω.2.2.2.1 _).2
            · rw [dif_neg hm]
              exact hcB

/-- The race chunks are nonempty lists. -/
theorem rchunk_ne_nil (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    (ω : RΩ A BL BR CC κ) {r : ℕ} (hr : r < mrace A BL BR CC κ) :
    rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r ≠ [] := by
  by_cases hr1 : r < A.m
  · rw [rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hr1]
    unfold reqMap
    intro hcon
    rw [List.map_eq_nil_iff] at hcon
    rw [chunkN_lt A ω.1 hr1] at hcon
    exact hchA ω.1 _ hcon
  · rw [not_lt] at hr1
    by_cases hr2 : r < A.m + κ
    · obtain ⟨j, rfl⟩ : ∃ j, r = A.m + j := ⟨r - A.m, by omega⟩
      have hj : j < κ := by omega
      rw [rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj]
      by_cases hb : ω.2.2.2.2 ⟨j, hj⟩
      · rw [if_pos hb]
        unfold parkMap
        intro hcon
        rw [List.map_eq_nil_iff] at hcon
        rw [chunkN_lt BL ω.2.1 (by
          have := cntL_le ω.2.2.2.2 (le_of_lt hj)
          omega)] at hcon
        exact hchL ω.2.1 _ hcon
      · rw [if_neg hb]
        unfold parkMap
        intro hcon
        rw [List.map_eq_nil_iff] at hcon
        rw [chunkN_lt BR ω.2.2.1 (by
          have := cntR_le ω.2.2.2.2 (le_of_lt hj)
          omega)] at hcon
        exact hchR ω.2.2.1 _ hcon
    · rw [not_lt] at hr2
      obtain ⟨k, rfl⟩ : ∃ k, r = A.m + κ + k := ⟨r - A.m - κ, by omega⟩
      rw [rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k]
      by_cases hs : survL A BL BR CC κ ω
      · rw [if_pos hs]
        have hremv : remCnt A BL BR CC κ ω = BL.m - cntL ω.2.2.2.2 κ := by
          unfold remCnt
          rw [if_pos hs]
        by_cases hk : k < remCnt A BL BR CC κ ω
        · rw [if_pos hk]
          unfold reqMap
          intro hcon
          rw [List.map_eq_nil_iff] at hcon
          rw [chunkN_lt BL ω.2.1 (by
            have := cntL_le ω.2.2.2.2 le_rfl
            omega)] at hcon
          exact hchL ω.2.1 _ hcon
        · rw [if_neg hk]
          by_cases hk2 : k - remCnt A BL BR CC κ ω < CC.m
          · rw [if_pos hk2]
            unfold reqMap
            intro hcon
            rw [List.map_eq_nil_iff] at hcon
            rw [chunkN_lt CC ω.2.2.2.1 hk2] at hcon
            exact hchC ω.2.2.2.1 _ hcon
          · rw [if_neg hk2]
            simp
      · rw [if_neg hs]
        have hsn : ¬ (survL A BL BR CC κ ω = true) := hs
        have hremv : remCnt A BL BR CC κ ω = BR.m - cntR ω.2.2.2.2 κ := by
          unfold remCnt
          rw [if_neg hsn]
        by_cases hk : k < remCnt A BL BR CC κ ω
        · rw [if_pos hk]
          unfold reqMap
          intro hcon
          rw [List.map_eq_nil_iff] at hcon
          rw [chunkN_lt BR ω.2.2.1 (by
            have := cntR_le ω.2.2.2.2 le_rfl
            omega)] at hcon
          exact hchR ω.2.2.1 _ hcon
        · rw [if_neg hk]
          by_cases hk2 : k - remCnt A BL BR CC κ ω < CC.m
          · rw [if_pos hk2]
            unfold reqMap
            intro hcon
            rw [List.map_eq_nil_iff] at hcon
            rw [chunkN_lt CC ω.2.2.2.1 hk2] at hcon
            exact hchC ω.2.2.2.1 _ hcon
          · rw [if_neg hk2]
            simp

end Assemble


section RaceSystem

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

open Classical in
/-- **The race**: the four constituent systems and the coin race assemble
into a chunk system on the target space, carrying the trivial-initial-
history, variance, and no-empty-chunk conjuncts.  The expected-total and
variance bounds enter as hypotheses (established separately). -/
theorem race_system (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πA πL πR πTL πTR : Y → X) (ιA ιL ιR ιTL ιTR : X → Y)
    (hπA : ∀ y z : Y, dist (πA y) (πA z) ≤ dist y z)
    (hπL : ∀ y z : Y, dist (πL y) (πL z) ≤ dist y z)
    (hπR : ∀ y z : Y, dist (πR y) (πR z) ≤ dist y z)
    (hπTL : ∀ y z : Y, dist (πTL y) (πTL z) ≤ dist y z)
    (hπTR : ∀ y z : Y, dist (πTR y) (πTR z) ≤ dist y z)
    (hGA : ∀ S : Set X, ∀ y ∈ GmA S, πA y ∈ S)
    (hGL : ∀ S : Set X, ∀ y ∈ GmL S, πL y ∈ S)
    (hGR : ∀ S : Set X, ∀ y ∈ GmR S, πR y ∈ S)
    (hGTL : ∀ S : Set X, ∀ y ∈ GmTL S, πTL y ∈ S)
    (hGTR : ∀ S : Set X, ∀ y ∈ GmTR S, πTR y ∈ S)
    (hGneA : ∀ S : Set X, S.Nonempty → (GmA S).Nonempty)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    (hGneTL : ∀ S : Set X, S.Nonempty → (GmTL S).Nonempty)
    (hGneTR : ∀ S : Set X, S.Nonempty → (GmTR S).Nonempty)
    (hιA : ∀ x y : X, dist (ιA x) (ιA y) ≤ dist x y)
    (hιL : ∀ x y : X, dist (ιL x) (ιL y) ≤ dist x y)
    (hιR : ∀ x y : X, dist (ιR x) (ιR y) ≤ dist x y)
    (hιTL : ∀ x y : X, dist (ιTL x) (ιTL y) ≤ dist x y)
    (hιTR : ∀ x y : X, dist (ιTR x) (ιTR y) ≤ dist x y)
    (hGAsub : ∀ S : Set X, ιA '' S ⊆ GmA S)
    (hGLsub : ∀ S : Set X, ιL '' S ⊆ GmL S)
    (hGRsub : ∀ S : Set X, ιR '' S ⊆ GmR S)
    (hGTLsub : ∀ S : Set X, ιTL '' S ⊆ GmTL S)
    (hGTRsub : ∀ S : Set X, ιTR '' S ⊆ GmTR S)
    (hJ1L : ιA t = ιL s) (hJ1R : ιA t = ιR s)
    (hJ2L : ιL t = ιTL s) (hJ2R : ιR t = ιTR s)
    (hJ3L : ιTL t = stopPt) (hJ3R : ιTR t = stopPt)
    (hTLt : GmTL {t} = {stopPt}) (hTRt : GmTR {t} = {stopPt})
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    {sep J p' : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J) (harith : J + pe ≤ sep)
    (hsepLR : ∀ SL SR : Set X, ∀ y ∈ GmL SL,
      ∀ z ∈ GmR SR, sep ≤ dist y z)
    (hdicho : ∀ z : Y,
      (z ∈ GmA ({t} : Set X) ∨ (∃ S, z ∈ GmL S) ∨ (∃ S, z ∈ GmR S)) →
      (∀ S' : Set X, ∀ p ∈ GmR S', sep ≤ dist z p)
      ∨ (∀ S' : Set X, ∀ p ∈ GmL S', sep ≤ dist z p))
    (h0A : ∀ a b : A.Ω, A.hist 0 a = A.hist 0 b)
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    (hcB : 0 ≤ cB)
    (hd3 : 3 * dist s t ≤ dist (ιA s) stopPt)
    {Trace Vrace : ℝ} {mLo' : ℕ} (hmLo : mLo' ≤ mrace A BL BR CC κ)
    (htot : Trace ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω (i : ℕ))
    (hvar : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω (i : ℕ))
          - ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
            * ∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω' (i : ℕ)) ^ 2 ≤ Vrace) :
    ∃ C' : ChunkSystemB Y (ιA s) stopPt 0 cB Trace p' mLo',
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ Vrace) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by
  refine ⟨{
    Ω := RΩ A BL BR CC κ
    instFin := inferInstance
    instDec := inferInstance
    P := RP A BL BR CC κ ε
    m := mrace A BL BR CC κ
    hist := fun r ω => rhist2 A BL BR CC κ ω r
    chunk := fun ω i =>
      rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ)
    size := fun ω i => rsize A BL BR CC κ ε ω (i : ℕ)
    hP := RP_pos A BL BR CC κ ε hε
    hPsum := RP_sum A BL BR CC κ ε hε
    hm := hmLo
    hm0 := by
      have := A.hm0
      unfold mrace
      omega
    href := fun i j hij ω ω' h =>
      rhist2_refine A BL BR CC κ hκL hκR hij ω ω' h
    hadapt := fun i ω ω' h =>
      rchunk_adapt A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        ω ω' h
    hsmeas := fun i ω ω' h =>
      rsize_smeas A BL BR CC κ ε hκL hκR h0L h0R ω ω' h
    hne := fun ω i =>
      race_ne A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
        hGneA hGneL hGneR hGneTL hGneTR ω (i : ℕ)
    hlast := fun ω =>
      race_last A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hTLt hTRt ω
    hopt := fun ω => le_trans
      (race_opt A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        ιA ιL ιR ιTL ιTR hιA hιL hιR hιTL hιTR hGAsub hGLsub hGRsub
        hGTLsub hGTRsub hJ1L hJ1R hJ2L hJ2R hJ3L hJ3R ω) hd3
    hsize := fun ω i =>
      rsize_bounds A BL BR CC κ ε hε hcB ω (i : ℕ)
    hcost := fun i ω₀ E bail =>
      race_hcost A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε hε hκL hκR
        πA πL πR πTL πTR hπA hπL hπR hπTL hπTR hGA hGL hGR hGTL hGTR
        hGneA hGneL hGneR hGneTL hGneTR hchA hchL hchR hchC
        hpe0 hpe hsep0 hdiam harith hsepLR hdicho h0L h0R ω₀ E bail
    htotal := htot }, ?_, ?_, ?_⟩
  · intro ω₁ ω₂
    show rhist2 A BL BR CC κ ω₁ 0 = rhist2 A BL BR CC κ ω₂ 0
    rw [rhist2_le_A A BL BR CC κ ω₁ (by omega),
      rhist2_le_A A BL BR CC κ ω₂ (by omega), h0A ω₁.1 ω₂.1]
  · exact hvar
  · intro ω i
    exact rchunk_ne_nil A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
      hκL hκR hchA hchL hchR hchC ω i.isLt

end RaceSystem


end Race

end KServer



-- Prove2me | Definitions.Def_KServer_race_step6
-- name    : KServer_race_step6
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T22:41:35.487943+00:00
-- url     : https://prove2.me/theorems/6a95cbbf-d0de-4477-8c56-55bd918e5224
-- title:
--   BCR level step, final form
-- statement:
--   The BCR level step on the theta gluing, final form: sturdy total 3T + G/2 minus the sides' depth-kappa L1 drawdowns and lower-order losses (no variance loss), exact chunk count, loose variance for downstream Chebyshev use, nonempty chunks, and the output invariants that propagate the recursion: L1-sturdiness and expected below-floor chunk counts at head-phase depths bounded by the head system's budgets.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound

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
import Definitions.Def_KServer_race_assemble
import Definitions.Def_KServer_race_fix
import Definitions.Def_KServer_race_fix2
import Definitions.Def_KServer_race_fix3
import Definitions.Def_KServer_race_sturdyout
import Definitions.Def_KServer_race_var3
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_race_sel
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_fold
import Definitions.Def_KServer_race_geo

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

open ThetaChain

/-- **The BCR level step, final form**: the sturdy total (no variance
loss), exact chunk count, loose variance, and the OUTPUT invariants at
head-phase depths: the produced system's L¹ drawdowns and expected
below-floor chunk counts up to depth `n₀ ≤ A.m` are bounded by the head
system's, so the sturdiness and bad-count budgets propagate to the next
level. -/
theorem race_step6 {X : Type*} [MetricSpace X] {s t : X} (hst : s ≠ t)
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) (hpe0 : 0 ≤ pe) {p' : ℝ} (hpe : pe ≤ p')
    (hpeD : dist s t + pe ≤ 2 * dist s t)
    (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    (hmean : ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i
      = ∑ r : BR.Ω, BR.P r * ∑ i, BR.size r i)
    {DL DR : ℝ}
    (hL1 : ∑ l : BL.Ω, BL.P l
      * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0 ≤ DL)
    (hR1 : ∑ r : BR.Ω, BR.P r
      * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0 ≤ DR)
    {n₀ : ℕ} (hn₀ : n₀ ≤ A.m) {DA BadA flo : ℝ}
    (hstA : ∀ n ≤ n₀, ∑ a : A.Ω, A.P a
      * max (A.expTotal - A.condExp A.totalSize n a) 0 ≤ DA)
    (hbadA : ∀ n ≤ n₀, ∑ a : A.Ω, A.P a
      * (∑ i ∈ Finset.range n,
          if A.sizeN i a < flo then (1 : ℝ) else 0) ≤ BadA)
    (h0A : ∀ a b : A.Ω, A.hist 0 a = A.hist 0 b)
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    {V G : ℝ} (hV0 : 0 ≤ V)
    (hVarA : ∑ a : A.Ω, A.P a * ((∑ i, A.size a i)
        - ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i) ^ 2 ≤ V)
    (hVarL : ∑ l : BL.Ω, BL.P l * ((∑ i, BL.size l i)
        - ∑ l' : BL.Ω, BL.P l' * ∑ i, BL.size l' i) ^ 2 ≤ V)
    (hVarR : ∑ r : BR.Ω, BR.P r * ((∑ i, BR.size r i)
        - ∑ r' : BR.Ω, BR.P r' * ∑ i, BR.size r' i) ^ 2 ≤ V)
    (hVarC : ∑ cc : CC.Ω, CC.P cc * ((∑ i, CC.size cc i)
        - ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i) ^ 2 ≤ V)
    (hG : G ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
    {mLo' : ℕ} (hmLo : mLo' ≤ mrace A BL BR CC κ) :
    letI := stepMetric s t hst
    ∃ C' : ChunkSystemB (Step s t hst) (stepS s t hst) (stepT s t hst)
        0 cB (3 * T + G / 2 - DL - DR - (κ : ℝ) * ε / 2
          - 2 * cB) p' mLo',
      C'.m = mrace A BL BR CC κ ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2
        ≤ V + (2 * V + 2 * (((κ : ℝ) + 1) * cB) * Real.sqrt (2 * V)
            + (((κ : ℝ) + 1) * cB) ^ 2)
          + (2 * V + 2 * cB ^ 2)) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ DA ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω
        * (∑ i ∈ Finset.range n,
            if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ BadA) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  refine race_system6 A BL BR CC (GA' s t hst) (GL' s t hst)
    (GR' s t hst) (GTL' s t hst) (GTR' s t hst) (stepT s t hst) κ ε
    hε hκL hκR
    (stepRet0 s t hst) (stepRet1 s t hst) (stepRet1 s t hst)
    (stepRet2 s t hst) (stepRet2 s t hst)
    (gL0 s t hst) (gR0 s t hst) (gL1 s t hst) (gR1 s t hst)
    (gL2 s t hst) (gR2 s t hst)
    (stepRet0_lipschitz s t hst) (stepRet1_lipschitz s t hst)
    (stepRet1_lipschitz s t hst) (stepRet2_lipschitz s t hst)
    (stepRet2_lipschitz s t hst)
    (hGA_ret s t hst) (hGL_ret s t hst) (hGR_ret s t hst)
    (hGTL_ret s t hst) (hGTR_ret s t hst)
    (hGA_ne s t hst) (hGL_ne s t hst) (hGR_ne s t hst)
    (hGTL_ne s t hst) (hGTR_ne s t hst)
    (gL0_nonexp s t hst) (gR0_nonexp s t hst) (gL1_nonexp s t hst)
    (gR1_nonexp s t hst) (gL2_nonexp s t hst) (gR2_nonexp s t hst)
    (hGAL_sub s t hst) (hGAR_sub s t hst)
    (fun S => Set.Subset.rfl) (fun S => Set.Subset.rfl)
    (fun S => Set.Subset.rfl) (fun S => Set.Subset.rfl)
    (gJ0 s t hst) (gJ1L s t hst) (gJ1R s t hst) (gJ2L s t hst)
    (gJ2R s t hst) (gJ3L s t hst) (gJ3R s t hst)
    (GTL'_t s t hst) (GTR'_t s t hst)
    hchA hchL hchR hchC
    (sep := 2 * dist s t) (J := dist s t) (p' := p')
    hpe0 hpe (by
      have := dist_pos.mpr hst
      linarith)
    (fun x₁ x₂ => taut_diam s t htaut x₁ x₂) hpeD
    (hsepLR_geo s t hst) (hdicho_geo s t hst)
    h0A h0L h0R hcB
    (hd3_geo s t hst)
    hn₀ hstA hbadA
    hmLo
    (race_total3 A BL BR CC κ ε hε hκL hκR hcB hL1 hR1 hG)
    (race_var3 A BL BR CC κ ε hε hκL hκR hcB hmean hVarA hVarL
      hVarR hVarC)

end Race

end KServer



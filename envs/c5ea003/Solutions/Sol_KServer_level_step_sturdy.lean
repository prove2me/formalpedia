-- Prove2me | solution 1 for KServer.level_step_sturdy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T23:58:06.360817+00:00
-- url     : https://prove2.me/submissions/1dbca7b7-86e4-4d3a-95a1-eb05410cb402

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_race_bad
import Definitions.Def_KServer_race_nbad
import Definitions.Def_KServer_race_step7
import Theorems.Thm_KServer_race_gain_bound2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

open KServer KServer.Race ThetaChain

section NbadFromBad

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}

/-- The expected bad coin-step count from the below-floor invariant of
the sides: marginalize the side bad-chunk counts. -/
theorem nbad_from_bad (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) {cLo' : ℝ} (hε : 0 < ε) (hεLo : ε ≤ cLo')
    {BadL BadR : ℝ}
    (hbadL : ∑ l : BL.Ω, BL.P l * (∑ i ∈ Finset.range κ,
        if BL.sizeN i l < cLo' then (1 : ℝ) else 0) ≤ BadL)
    (hbadR : ∑ r : BR.Ω, BR.P r * (∑ i ∈ Finset.range κ,
        if BR.sizeN i r < cLo' then (1 : ℝ) else 0) ≤ BadR) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * Nbad A BL BR CC κ cLo' ω
      ≤ 2 * (BadL + BadR) := by
  refine le_trans (Nbad_le A BL BR CC κ ε cLo' hε hεLo) ?_
  have hmarg : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ)
      = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
          * (badCount cLo' BL l κ + badCount cLo' BR r κ) :=
    RP_margLR A BL BR CC κ ε hε
      (fun l r => badCount cLo' BL l κ + badCount cLo' BR r κ)
  have hrow : ∀ l : BL.Ω,
      ∑ r : BR.Ω, BL.P l * BR.P r
        * (badCount cLo' BL l κ + badCount cLo' BR r κ)
      = BL.P l * badCount cLo' BL l κ
        + BL.P l * (∑ r : BR.Ω, BR.P r * badCount cLo' BR r κ) := by
    intro l
    rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) =>
      show BL.P l * BR.P r
          * (badCount cLo' BL l κ + badCount cLo' BR r κ)
        = BL.P l * badCount cLo' BL l κ * BR.P r
          + BL.P l * (BR.P r * badCount cLo' BR r κ)
        from by ring),
      Finset.sum_add_distrib]
    congr 1
    · exact sum_P_mul BR.P BR.hPsum
        (BL.P l * badCount cLo' BL l κ) _ (fun r => by ring)
    · rw [Finset.mul_sum]
  have hsplit : ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
      * (badCount cLo' BL l κ + badCount cLo' BR r κ)
      = (∑ l : BL.Ω, BL.P l * badCount cLo' BL l κ)
        + ∑ r : BR.Ω, BR.P r * badCount cLo' BR r κ := by
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hrow l,
      Finset.sum_add_distrib]
    congr 1
    exact sum_P_mul BL.P BL.hPsum
      (∑ r : BR.Ω, BR.P r * badCount cLo' BR r κ) _ (fun l => by ring)
  have hL' : ∑ l : BL.Ω, BL.P l * badCount cLo' BL l κ ≤ BadL := hbadL
  have hR' : ∑ r : BR.Ω, BR.P r * badCount cLo' BR r κ ≤ BadR := hbadR
  rw [hmarg, hsplit]
  linarith

end NbadFromBad

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    (hst : s ≠ t)
    (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    {c T p V D Bad flo : ℝ} {M n₀ : ℕ}
    (C : KServer.ChunkSystemB X s t 0 c T p M) (hm : C.m = M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hsturdy : C.SturdyL1 n₀ D)
    (hbad : ∀ n ≤ n₀, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ Bad)
    (hch : ∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ [])
    {ε G T3 V3 p'' : ℝ} {κ : ℕ}
    (hε : 0 < ε) (hεLo : ε ≤ flo) (hLoc : flo ≤ c + ε)
    (hc0 : 0 ≤ c) (hp0 : 0 ≤ p) (hpp'' : p ≤ p'')
    (hpD : p ≤ dist s t)
    (hκn₀ : κ ≤ n₀) (hn₀M : n₀ ≤ M)
    (hV0 : 0 ≤ V)
    (hG : G ≤ Real.sqrt (((κ : ℝ) * flo ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (c + ε) ^ 2) ^ 2
          + 3 * (c + ε) ^ 2 * ((κ : ℝ) * (c + ε) ^ 2)))
      - (κ : ℝ) * ε - (c + ε + flo) * (4 * Bad))
    (hT3 : T3 ≤ 3 * T + G / 2 - 2 * D - (κ : ℝ) * ε / 2 - 2 * c)
    (hV3 : 6 * V + 8 * (κ : ℝ) * (c + ε) ^ 2
      + 5 * ((κ : ℝ) * ε) ^ 2 + 10 * ((κ : ℝ) * ε / 2 + c) ^ 2
      + 2 * c ^ 2 ≤ V3) :
    letI := stepMetric s t hst
    ∃ C' : KServer.ChunkSystemB (Step s t hst) (stepS s t hst)
        (stepT s t hst) 0 c T3 p'' (3 * M + κ),
      C'.m = 3 * M + κ ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V3) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ D ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ Bad) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  have hκM : κ ≤ C.m := by
    rw [hm]
    omega
  have hn₀A : n₀ ≤ C.m := by
    rw [hm]
    exact hn₀M
  -- the anti-concentration gain via the below-floor invariant
  have hbadκ : ∑ ω, C.P ω * (∑ i ∈ Finset.range κ,
      if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ Bad := hbad κ hκn₀
  have hNb : ∑ ω : RΩ C C C C κ, RP C C C C κ ε ω
      * Nbad C C C C κ flo ω ≤ 4 * Bad := by
    have h1 := nbad_from_bad C C C C κ ε hε hεLo hbadκ hbadκ
    linarith
  have hGain := KServer.race_gain_bound2 C C C C κ ε hε hc0 hεLo hLoc hNb
  have hG' : G ≤ ∑ ω : RΩ C C C C κ, RP C C C C κ ε ω
      * |sumL C C C C κ ω - sumR C C C C κ ω| :=
    le_trans hG hGain
  -- the sturdiness inputs of the race
  have hL1 : ∑ l : C.Ω, C.P l
      * max (C.expTotal - C.condExp C.totalSize κ l) 0 ≤ D :=
    hsturdy κ hκn₀
  have hpeD : dist s t + p ≤ 2 * dist s t := by linarith
  have hmrace : mrace C C C C κ = 3 * M + κ := by
    unfold mrace
    rw [hm, max_self]
    omega
  have hmLo : 3 * M + κ ≤ mrace C C C C κ := le_of_eq hmrace.symm
  have hmean : (∑ l : C.Ω, C.P l * ∑ i, C.size l i)
      = ∑ r : C.Ω, C.P r * ∑ i, C.size r i := rfl
  obtain ⟨C3, hm3, h0triv3, hVar3, hch3, hsty3, hbad3⟩ :=
    race_step7 hst C C C C κ ε hε hκM hκM hc0 hp0 hpp'' hpeD htaut hmean
      hL1 hL1 hn₀A hsturdy hbad h0triv h0triv h0triv hch hch hch hch hV0
      hVar hVar hVar hVar hG' hmLo
  -- lower the total to T3 and repackage
  have hT3' : T3 ≤ 3 * T + G / 2 - D - D - (κ : ℝ) * ε / 2 - 2 * c := by
    linarith
  refine ⟨C3.adjust (le_refl 0) (le_refl c) hT3' (le_refl p'')
    (le_refl (3 * M + κ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [KServer.ChunkSystemB.adjust_m, hm3, hmrace]
  · intro ω₁ ω₂
    exact h0triv3 ω₁ ω₂
  · refine le_trans hVar3 ?_
    linarith
  · exact hch3
  · exact KServer.ChunkSystemB.SturdyL1.adjust (le_refl 0) (le_refl c)
      hT3' (le_refl p'') (le_refl (3 * M + κ)) hsty3
  · exact hbad3

-- Prove2me | Theorems.Thm_KServer_level_step_sturdy
-- name    : KServer.level_step_sturdy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T23:56:09.826661+00:00
-- url     : https://prove2.me/theorems/5021520d-58e2-4fd0-9bf7-2c08b59aedc6
-- title:
--   The sturdy BCR level step: race with invariant pass-through
-- statement:
--   The sturdy BCR level step. Given a chunk system C on a taut metric space (every point lies between the marked endpoints s and t) with M chunks of sizes in [0, c], expected total at least T, variance at most V, L1-sturdiness (expected Doob drawdown of the total at every depth up to n0 at most D), and at most Bad expected below-floor chunks (floor flo) among the first n0, the race construction on the theta step produces a system on the extended metric space Step(s,t) with exactly 3M + kappa chunks whose expected total is at least 3T + G/2 - 2D - kappa*eps/2 - 2c, where the gain G comes from martingale anti-concentration of the side-race imbalance: G is at most sqrt((kappa*flo^2)^3 / (8(kappa(c+eps)^2)^2 + 3(c+eps)^2(kappa(c+eps)^2))) - kappa*eps - (c+eps+flo)*(4*Bad), with the expected number of bad coin steps bounded by 4*Bad through the below-floor invariant of the sides. The output variance is at most 6V + 8*kappa*(c+eps)^2 + 5*(kappa*eps)^2 + 10*(kappa*eps/2+c)^2 + 2c^2 (the martingale-form race variance), the output retains chunk-nonemptiness and a trivial time-0 history, and both invariants pass through UNCHANGED: the output is L1-sturdy at depths up to n0 with the same drawdown bound D, and its expected below-floor count up to depth n0 is still at most Bad, because at head-phase depths the race atoms coincide with the head atoms and the other phases are independent. The selection loss of the survivor race is financed by the sturdiness bound (2D) instead of the variance (no sqrt(V) loss).
-- source:
--   Bartal-Chrobak-Rasala lower bound program: sturdy level step

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_fold
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_geo

namespace KServer

open Race ThetaChain

theorem level_step_sturdy {X : Type*} [MetricSpace X] {s t : X}
    (hst : s ≠ t)
    (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    {c T p V D Bad flo : ℝ} {M n₀ : ℕ}
    (C : ChunkSystemB X s t 0 c T p M) (hm : C.m = M)
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
    ∃ C' : ChunkSystemB (Step s t hst) (stepS s t hst)
        (stepT s t hst) 0 c T3 p'' (3 * M + κ),
      C'.m = 3 * M + κ ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V3) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ D ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ Bad) := by
  sorry

end KServer

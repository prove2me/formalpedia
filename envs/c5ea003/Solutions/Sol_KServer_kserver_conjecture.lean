-- Prove2me | solution 1 for KServer.kserver_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:11:32.562271+00:00
-- url     : https://prove2.me/submissions/14035e61-c765-44ed-a7fb-4371ac27c511
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_online_cost_compactness
import Theorems.Thm_KServer_finite_horizon_uniform_bound

set_option autoImplicit false
open KServer

/-- Reduce the deterministic conjecture to uniform bounds for finite games. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by
  classical
  obtain ⟨a, ha⟩ := KServer.finite_horizon_uniform_bound k hk M C₀
  have hfinite (F : Finset (List M)) : ∃ A : OnlineAlgorithm k M,
      A.conf [] = C₀ ∧
      ∀ σ ∈ F, A.cost σ ≤ (k : ℝ) * offlineCost C₀ σ + a := by
    let P : Finset M := F.biUnion List.toFinset
    let n : ℕ := F.sup List.length
    obtain ⟨A, hA0, hA⟩ := ha P n
    refine ⟨A, hA0, ?_⟩
    intro σ hσ
    apply hA σ (Finset.le_sup (f := List.length) hσ)
    intro r hr
    exact Finset.mem_biUnion.mpr ⟨σ, hσ, List.mem_toFinset.mpr hr⟩
  obtain ⟨A, hA0, hA⟩ := KServer.online_cost_compactness k M C₀
    (fun σ => (k : ℝ) * offlineCost C₀ σ + a) hfinite
  refine ⟨A, hA0, a, ?_⟩
  intro σ
  simpa only [hA0] using hA σ

#print axioms solution

-- Prove2me | solution 1 for KServer.antipodal_coalesced_growth_sum_sharp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-07T10:33:37.875725+00:00
-- url     : https://prove2.me/submissions/b35cd1e0-f572-4b66-ae87-b6e845e32030
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k
import Theorems.Thm_KServer_ckPotK_step_antipode
import Theorems.Thm_KServer_ckPotK_le_offline
import Theorems.Thm_KServer_ckPotK_nil_coalesced

open KServer

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (p : M) (σ : List M) :
    ∑ t ∈ Finset.range σ.length,
        (@workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take (t + 1)).map Sum.inl) (fun _ => Sum.inr (σ.getD t p))
          - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take t).map Sum.inl) (fun _ => Sum.inr (σ.getD t p)))
      ≤ ((k : ℝ) + 1) * offlineCost (fun _ : Fin k => p) σ := by
  have key : ∀ t : ℕ, t < σ.length → σ.take (t + 1) = σ.take t ++ [σ.getD t p] := by
    intro t ht
    rw [List.take_add_one]
    simp [List.getElem?_eq_getElem ht]
  have hstep : ∀ t ∈ Finset.range σ.length,
      (@workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take (t + 1)).map Sum.inl) (fun _ => Sum.inr (σ.getD t p))
          - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take t).map Sum.inl) (fun _ => Sum.inr (σ.getD t p)))
        ≤ ckPotK k M Δ hΔ0 hΔ (fun _ => p) (σ.take (t + 1))
          - ckPotK k M Δ hΔ0 hΔ (fun _ => p) (σ.take t) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [key t ht]
    exact ckPotK_step_antipode k (by omega) M Δ hΔ0 hΔ (fun _ => p) (σ.take t) (σ.getD t p)
  have htel :
      ∑ t ∈ Finset.range σ.length,
          (ckPotK k M Δ hΔ0 hΔ (fun _ => p) (σ.take (t + 1))
            - ckPotK k M Δ hΔ0 hΔ (fun _ => p) (σ.take t))
        = ckPotK k M Δ hΔ0 hΔ (fun _ => p) σ - Δ * (k : ℝ) * ((k : ℝ) + 1) := by
    rw [Finset.sum_range_sub (fun t => ckPotK k M Δ hΔ0 hΔ (fun _ => p) (σ.take t)) σ.length]
    rw [List.take_length, List.take_zero, ckPotK_nil_coalesced k M Δ hΔ0 hΔ p]
  have hbound := ckPotK_le_offline k (by omega) M Δ hΔ0 hΔ (fun _ : Fin k => p) σ
  calc ∑ t ∈ Finset.range σ.length,
        (@workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take (t + 1)).map Sum.inl) (fun _ => Sum.inr (σ.getD t p))
          - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take t).map Sum.inl) (fun _ => Sum.inr (σ.getD t p)))
      ≤ ∑ t ∈ Finset.range σ.length,
          (ckPotK k M Δ hΔ0 hΔ (fun _ => p) (σ.take (t + 1))
            - ckPotK k M Δ hΔ0 hΔ (fun _ => p) (σ.take t)) := Finset.sum_le_sum hstep
    _ = ckPotK k M Δ hΔ0 hΔ (fun _ => p) σ - Δ * (k : ℝ) * ((k : ℝ) + 1) := htel
    _ ≤ ((k : ℝ) + 1) * offlineCost (fun _ : Fin k => p) σ := by linarith

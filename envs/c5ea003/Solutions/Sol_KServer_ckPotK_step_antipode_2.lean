-- Prove2me | solution 2 for KServer.ckPotK_step_antipode
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-09T16:12:38.093198+00:00
-- url     : https://prove2.me/submissions/016a12f0-2c8b-469e-86c4-f4d2cb112b69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_ck_potential_k
import Theorems.Thm_KServer_ckPotAtK_snoc_of_anchor_last
import Theorems.Thm_KServer_ckPotK_anchor_violation_antitone

open KServer

/-- The step inequality of the Coester–Koutsoupias potential, reduced to the statement
that the anchor violation at the request does not increase when the request is served. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        ((l ++ [r]).map Sum.inl) (fun _ => Sum.inr r)
      - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        (l.map Sum.inl) (fun _ => Sum.inr r)
      ≤ ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) - ckPotK k M Δ hΔ0 hΔ C₀ l := by
  classical
  have hk0 : 0 < k := hk
  haveI : Nonempty M := ⟨C₀ ⟨0, hk0⟩⟩
  haveI : Nonempty (Fin k → M) := ⟨fun _ => C₀ ⟨0, hk0⟩⟩
  set G : ℝ :=
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        ((l ++ [r]).map Sum.inl) (fun _ => Sum.inr r)
      - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        (l.map Sum.inl) (fun _ => Sum.inr r) with hG
  -- every anchor tuple whose last coordinate is `r` has its potential shifted by exactly `G`
  have hshift : ∀ x : Fin k → M,
      ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) (Function.update x ⟨k - 1, by omega⟩ r)
        = ckPotAtK k M Δ hΔ0 hΔ C₀ l (Function.update x ⟨k - 1, by omega⟩ r) + G := by
    intro x
    have hxr : (Function.update x (⟨k - 1, by omega⟩ : Fin k) r) ⟨k - 1, by omega⟩ = r :=
      Function.update_self (⟨k - 1, by omega⟩ : Fin k) r x
    have h := ckPotAtK_snoc_of_anchor_last k hk M Δ hΔ0 hΔ C₀ l r
      (Function.update x (⟨k - 1, by omega⟩ : Fin k) r) hxr
    rw [← hG] at h
    linarith
  have hA : (⨅ x : Fin k → M, ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r])
        (Function.update x ⟨k - 1, by omega⟩ r))
      = (⨅ x : Fin k → M, ckPotAtK k M Δ hΔ0 hΔ C₀ l
        (Function.update x ⟨k - 1, by omega⟩ r)) + G := by
    have hbdd : BddBelow (Set.range fun x : Fin k → M =>
        ckPotAtK k M Δ hΔ0 hΔ C₀ l (Function.update x ⟨k - 1, by omega⟩ r)) :=
      (Set.finite_range _).bddBelow
    rw [iInf_congr hshift]
    exact (ciInf_add hbdd G).symm
  have hchild := ckPotK_anchor_violation_antitone k hk M Δ hΔ0 hΔ C₀ l r
  rw [hA] at hchild
  linarith

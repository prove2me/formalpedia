-- Prove2me | solution 1 for KServer.workFnU_duality_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T19:46:37.047441+00:00
-- url     : https://prove2.me/submissions/4e96ed71-362c-4098-ab34-9487887c5ca2

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_duality

open KServer

/-- **The duality lemma as an equivalence.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M) :
    (∀ X : Config k M,
        workFnU C₀ σ A - ∑ i, dist r (A i) ≤ workFnU C₀ σ X - ∑ i, dist r (X i))
      ↔ ((∀ X : Config k M,
            workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
              ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i))
          ∧ (∀ X : Config k M,
            workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
              ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A)) := by
  constructor
  · intro hA
    exact workFnU_duality k hk M C₀ σ r A hA
  · rintro ⟨h1, h2⟩ X
    have a1 := h1 X
    have a2 := h2 X
    linarith

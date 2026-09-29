-- Prove2me | solution 1 for IdempotentRenormalizationDuality.minimal_flows_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:03:01.793809+00:00
-- url     : https://prove2.me/submissions/868d667f-838f-42f3-b36f-e8bfb9435c91

import Mathlib
import Definitions.Def_Bridges_IdempotentRenormalizationDuality
open IdempotentRenormalizationDuality in
theorem solution {S C : Type*} [Fintype S] [LinearOrder S] [DecidableEq S] [Fintype C]
    [DecidableEq C] (RG₁ RG₂ : ScaleClosureSystem S C)
    (_hmin₁ : RG₁.IsMinimalFlow)
    (_hmin₂ : RG₂.IsMinimalFlow)
    (htransfer : ∀ s t (h : s ≤ t) v,
      RG₁.transfer s t h v = RG₂.transfer s t h v)
    (hclosed : ∀ s a, (RG₁.cl s).IsClosed a ↔ (RG₂.cl s).IsClosed a) :
    Nonempty (ScalePreservingIso RG₁ RG₂) := by
  -- closure operators with the same closed sets coincide (closure = least closed superset)
  have hcl : ∀ s a, (RG₂.cl s).cl a = (RG₁.cl s).cl a := by
    intro s a
    apply Finset.Subset.antisymm
    · have h1 : (RG₂.cl s).IsClosed ((RG₁.cl s).cl a) := (hclosed s _).1 ((RG₁.cl s).idem a)
      calc (RG₂.cl s).cl a ⊆ (RG₂.cl s).cl ((RG₁.cl s).cl a) :=
            (RG₂.cl s).mono ((RG₁.cl s).extensive a)
        _ = (RG₁.cl s).cl a := h1
    · have h2 : (RG₁.cl s).IsClosed ((RG₂.cl s).cl a) := (hclosed s _).2 ((RG₂.cl s).idem a)
      calc (RG₁.cl s).cl a ⊆ (RG₁.cl s).cl ((RG₂.cl s).cl a) :=
            (RG₁.cl s).mono ((RG₂.cl s).extensive a)
        _ = (RG₂.cl s).cl a := h2
  -- so the identity relabelling is a scale-preserving isomorphism
  exact ⟨{ toEquiv := Equiv.refl C,
           closure_compat := fun s a => by simp [hcl],
           transfer_compat := fun s t h a => by simp [htransfer] }⟩

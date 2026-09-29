-- Prove2me | solution 2 for EmergentGeometry.throat_comm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:54:23.152423+00:00
-- url     : https://prove2.me/submissions/7a5232a8-356c-4d96-8d3e-803bfd99c2b5

import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : BulkGraph V) (A B : Region V) :
    throat G A B = throat G B A := by
  have hmem : ∀ (X Y f : Region V), f ∈ sepSet X Y → (fun v => !(f v)) ∈ sepSet Y X := by
    intro X Y f hf
    simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Separates] at hf ⊢
    exact ⟨fun v hv => by simp [hf.2 v hv], fun v hv => by simp [hf.1 v hv]⟩
  have hw : ∀ f : Region V, cutWeight G (fun v => !(f v)) = cutWeight G f := by
    intro f
    simp only [cutWeight]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    congr 1
    cases hu : f u <;> cases hv : f v <;> simp [sepBit]
  have hne : (sepSet A B).Nonempty → (sepSet B A).Nonempty := by
    rintro ⟨f, hf⟩
    exact ⟨_, hmem A B f hf⟩
  have hne' : (sepSet B A).Nonempty → (sepSet A B).Nonempty := by
    rintro ⟨f, hf⟩
    exact ⟨_, hmem B A f hf⟩
  unfold throat
  by_cases h : (sepSet A B).Nonempty
  · rw [dif_pos h, dif_pos (hne h)]
    apply le_antisymm
    · refine Finset.le_inf' _ _ (fun f hf => ?_)
      calc (sepSet A B).inf' h (cutWeight G)
          ≤ cutWeight G (fun v => !(f v)) := Finset.inf'_le _ (hmem B A f hf)
        _ = cutWeight G f := hw f
    · refine Finset.le_inf' _ _ (fun f hf => ?_)
      calc (sepSet B A).inf' (hne h) (cutWeight G)
          ≤ cutWeight G (fun v => !(f v)) := Finset.inf'_le _ (hmem A B f hf)
        _ = cutWeight G f := hw f
  · rw [dif_neg h, dif_neg (fun hh => h (hne' hh))]

-- Prove2me | solution 2 for EmergentGeometry.entropy_complement
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:13:04.422624+00:00
-- url     : https://prove2.me/submissions/ede295b1-e02a-4d2c-a6bd-93bfefa27637

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (M : HoloModel V) (A : Region V) :
    entropy M (fun v => M.bdry v && !(A v)) = entropy M A := by
  have hcw : ∀ f : Region V,
      cutWeight M.toBulkGraph (fun v => !(f v)) = cutWeight M.toBulkGraph f := by
    intro f
    simp only [cutWeight]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    congr 1
    cases hu : f u <;> cases hv : f v <;> simp [sepBit]
  have hmem1 : ∀ f : Region V, f ∈ admSet M A →
      (fun v => !(f v)) ∈ admSet M (fun v => M.bdry v && !(A v)) := by
    intro f hf
    rw [mem_admSet]
    intro v hv
    show (!(f v)) = (M.bdry v && !(A v))
    rw [(mem_admSet.mp hf) v hv, hv]
    simp
  have hmem2 : ∀ f : Region V, f ∈ admSet M (fun v => M.bdry v && !(A v)) →
      (fun v => !(f v)) ∈ admSet M A := by
    intro f hf
    rw [mem_admSet]
    intro v hv
    show (!(f v)) = A v
    have hfv := (mem_admSet.mp hf) v hv
    simp only [hv, Bool.true_and] at hfv
    rw [hfv]
    simp
  apply le_antisymm
  · obtain ⟨f, hf, hfeq⟩ :=
      Finset.exists_mem_eq_inf' (admSet_nonempty M A) (cutWeight M.toBulkGraph)
    calc entropy M (fun v => M.bdry v && !(A v))
        ≤ cutWeight M.toBulkGraph (fun v => !(f v)) := Finset.inf'_le _ (hmem1 f hf)
      _ = cutWeight M.toBulkGraph f := hcw f
      _ = entropy M A := hfeq.symm
  · obtain ⟨f, hf, hfeq⟩ :=
      Finset.exists_mem_eq_inf' (admSet_nonempty M (fun v => M.bdry v && !(A v)))
        (cutWeight M.toBulkGraph)
    calc entropy M A
        ≤ cutWeight M.toBulkGraph (fun v => !(f v)) := Finset.inf'_le _ (hmem2 f hf)
      _ = cutWeight M.toBulkGraph f := hcw f
      _ = entropy M (fun v => M.bdry v && !(A v)) := hfeq.symm

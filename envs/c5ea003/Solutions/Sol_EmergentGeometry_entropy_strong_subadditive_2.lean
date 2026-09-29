-- Prove2me | solution 2 for EmergentGeometry.entropy_strong_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:18:44.963781+00:00
-- url     : https://prove2.me/submissions/0dadb55b-c029-4ade-acb6-efcfe031b02b

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (M : HoloModel V) (A B C : Region V)
    (hAC : ∀ v, A v = true → C v = false) :
    entropy M (fun v => A v || B v || C v) + entropy M B
      ≤ entropy M (fun v => A v || B v) + entropy M (fun v => B v || C v) := by
  have hsub : ∀ f g : Region V,
      cutWeight M.toBulkGraph (fun v => f v && g v)
        + cutWeight M.toBulkGraph (fun v => f v || g v)
      ≤ cutWeight M.toBulkGraph f + cutWeight M.toBulkGraph g := by
    intro f g
    have hpt : ∀ a1 a2 b1 b2 : Bool,
        (sepBit (a1 && b1) (a2 && b2) : ℝ) + (sepBit (a1 || b1) (a2 || b2) : ℝ)
          ≤ (sepBit a1 a2 : ℝ) + (sepBit b1 b2 : ℝ) := by
      intro a1 a2 b1 b2
      cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> norm_num [sepBit]
    have key : ∀ u v : V,
        (sepBit (f u && g u) (f v && g v) : ℝ) * M.toBulkGraph.weight u v
          + (sepBit (f u || g u) (f v || g v) : ℝ) * M.toBulkGraph.weight u v
        ≤ (sepBit (f u) (f v) : ℝ) * M.toBulkGraph.weight u v + (sepBit (g u) (g v) : ℝ) * M.toBulkGraph.weight u v := by
      intro u v
      have h := hpt (f u) (f v) (g u) (g v)
      nlinarith [M.toBulkGraph.weight_nonneg u v]
    have hrow : ∀ u : V,
        (∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * M.toBulkGraph.weight u v)
          + (∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * M.toBulkGraph.weight u v)
        ≤ (∑ v : V, (sepBit (f u) (f v) : ℝ) * M.toBulkGraph.weight u v)
          + (∑ v : V, (sepBit (g u) (g v) : ℝ) * M.toBulkGraph.weight u v) := by
      intro u
      calc (∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * M.toBulkGraph.weight u v)
            + (∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * M.toBulkGraph.weight u v)
          = ∑ v : V, ((sepBit (f u && g u) (f v && g v) : ℝ) * M.toBulkGraph.weight u v
              + (sepBit (f u || g u) (f v || g v) : ℝ) * M.toBulkGraph.weight u v) :=
            Finset.sum_add_distrib.symm
        _ ≤ ∑ v : V, ((sepBit (f u) (f v) : ℝ) * M.toBulkGraph.weight u v
              + (sepBit (g u) (g v) : ℝ) * M.toBulkGraph.weight u v) :=
            Finset.sum_le_sum (fun v _ => key u v)
        _ = (∑ v : V, (sepBit (f u) (f v) : ℝ) * M.toBulkGraph.weight u v)
              + (∑ v : V, (sepBit (g u) (g v) : ℝ) * M.toBulkGraph.weight u v) := Finset.sum_add_distrib
    have hsum : (∑ u : V, ∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * M.toBulkGraph.weight u v)
        + (∑ u : V, ∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * M.toBulkGraph.weight u v)
        ≤ (∑ u : V, ∑ v : V, (sepBit (f u) (f v) : ℝ) * M.toBulkGraph.weight u v)
          + (∑ u : V, ∑ v : V, (sepBit (g u) (g v) : ℝ) * M.toBulkGraph.weight u v) := by
      calc (∑ u : V, ∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * M.toBulkGraph.weight u v)
            + (∑ u : V, ∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * M.toBulkGraph.weight u v)
          = ∑ u : V, ((∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * M.toBulkGraph.weight u v)
              + (∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * M.toBulkGraph.weight u v)) :=
            Finset.sum_add_distrib.symm
        _ ≤ ∑ u : V, ((∑ v : V, (sepBit (f u) (f v) : ℝ) * M.toBulkGraph.weight u v)
              + (∑ v : V, (sepBit (g u) (g v) : ℝ) * M.toBulkGraph.weight u v)) :=
            Finset.sum_le_sum (fun u _ => hrow u)
        _ = (∑ u : V, ∑ v : V, (sepBit (f u) (f v) : ℝ) * M.toBulkGraph.weight u v)
              + (∑ u : V, ∑ v : V, (sepBit (g u) (g v) : ℝ) * M.toBulkGraph.weight u v) :=
            Finset.sum_add_distrib
    simp only [cutWeight]
    linarith
  obtain ⟨f, hf, hfeq⟩ :=
    Finset.exists_mem_eq_inf' (admSet_nonempty M (fun v => A v || B v)) (cutWeight M.toBulkGraph)
  obtain ⟨g, hg, hgeq⟩ :=
    Finset.exists_mem_eq_inf' (admSet_nonempty M (fun v => B v || C v)) (cutWeight M.toBulkGraph)
  have hadm1 : (fun v => f v || g v) ∈ admSet M (fun v => A v || B v || C v) := by
    rw [mem_admSet]
    intro v hv
    show (f v || g v) = (A v || B v || C v)
    rw [(mem_admSet.mp hf) v hv, (mem_admSet.mp hg) v hv]
    show ((A v || B v) || (B v || C v)) = (A v || B v || C v)
    cases A v <;> cases B v <;> cases C v <;> rfl
  have hadm2 : (fun v => f v && g v) ∈ admSet M B := by
    rw [mem_admSet]
    intro v hv
    show (f v && g v) = B v
    rw [(mem_admSet.mp hf) v hv, (mem_admSet.mp hg) v hv]
    show ((A v || B v) && (B v || C v)) = B v
    have h := hAC v
    cases hA : A v <;> cases hB : B v <;> cases hC : C v <;> simp_all
  have h1 : entropy M (fun v => A v || B v || C v)
      ≤ cutWeight M.toBulkGraph (fun v => f v || g v) := Finset.inf'_le _ hadm1
  have h2 : entropy M B ≤ cutWeight M.toBulkGraph (fun v => f v && g v) :=
    Finset.inf'_le _ hadm2
  have h3 := hsub f g
  have hA : entropy M (fun v => A v || B v) = cutWeight M.toBulkGraph f := hfeq
  have hB : entropy M (fun v => B v || C v) = cutWeight M.toBulkGraph g := hgeq
  linarith

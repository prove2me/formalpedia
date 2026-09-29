-- Prove2me | solution 1 for EmergentGeometry.cutWeight_submodular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:28:51.727741+00:00
-- url     : https://prove2.me/submissions/dd5b82f0-28f3-4f3c-ae15-314c249ac430

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] (G : BulkGraph V) (f g : Region V) :
    cutWeight G (fun v => f v && g v) + cutWeight G (fun v => f v || g v)
      ≤ cutWeight G f + cutWeight G g := by
  have hpt : ∀ a1 a2 b1 b2 : Bool,
      (sepBit (a1 && b1) (a2 && b2) : ℝ) + (sepBit (a1 || b1) (a2 || b2) : ℝ)
        ≤ (sepBit a1 a2 : ℝ) + (sepBit b1 b2 : ℝ) := by
    intro a1 a2 b1 b2
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> norm_num [sepBit]
  have key : ∀ u v : V,
      (sepBit (f u && g u) (f v && g v) : ℝ) * G.weight u v
        + (sepBit (f u || g u) (f v || g v) : ℝ) * G.weight u v
      ≤ (sepBit (f u) (f v) : ℝ) * G.weight u v + (sepBit (g u) (g v) : ℝ) * G.weight u v := by
    intro u v
    have h := hpt (f u) (f v) (g u) (g v)
    nlinarith [G.weight_nonneg u v]
  have hrow : ∀ u : V,
      (∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * G.weight u v)
        + (∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * G.weight u v)
      ≤ (∑ v : V, (sepBit (f u) (f v) : ℝ) * G.weight u v)
        + (∑ v : V, (sepBit (g u) (g v) : ℝ) * G.weight u v) := by
    intro u
    calc (∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * G.weight u v)
          + (∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * G.weight u v)
        = ∑ v : V, ((sepBit (f u && g u) (f v && g v) : ℝ) * G.weight u v
            + (sepBit (f u || g u) (f v || g v) : ℝ) * G.weight u v) :=
          Finset.sum_add_distrib.symm
      _ ≤ ∑ v : V, ((sepBit (f u) (f v) : ℝ) * G.weight u v
            + (sepBit (g u) (g v) : ℝ) * G.weight u v) :=
          Finset.sum_le_sum (fun v _ => key u v)
      _ = (∑ v : V, (sepBit (f u) (f v) : ℝ) * G.weight u v)
            + (∑ v : V, (sepBit (g u) (g v) : ℝ) * G.weight u v) := Finset.sum_add_distrib
  have hsum : (∑ u : V, ∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * G.weight u v)
      + (∑ u : V, ∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * G.weight u v)
      ≤ (∑ u : V, ∑ v : V, (sepBit (f u) (f v) : ℝ) * G.weight u v)
        + (∑ u : V, ∑ v : V, (sepBit (g u) (g v) : ℝ) * G.weight u v) := by
    calc (∑ u : V, ∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * G.weight u v)
          + (∑ u : V, ∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * G.weight u v)
        = ∑ u : V, ((∑ v : V, (sepBit (f u && g u) (f v && g v) : ℝ) * G.weight u v)
            + (∑ v : V, (sepBit (f u || g u) (f v || g v) : ℝ) * G.weight u v)) :=
          Finset.sum_add_distrib.symm
      _ ≤ ∑ u : V, ((∑ v : V, (sepBit (f u) (f v) : ℝ) * G.weight u v)
            + (∑ v : V, (sepBit (g u) (g v) : ℝ) * G.weight u v)) :=
          Finset.sum_le_sum (fun u _ => hrow u)
      _ = (∑ u : V, ∑ v : V, (sepBit (f u) (f v) : ℝ) * G.weight u v)
            + (∑ u : V, ∑ v : V, (sepBit (g u) (g v) : ℝ) * G.weight u v) :=
          Finset.sum_add_distrib
  simp only [cutWeight]
  linarith

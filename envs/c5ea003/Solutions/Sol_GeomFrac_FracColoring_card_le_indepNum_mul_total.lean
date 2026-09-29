-- Prove2me | solution 1 for GeomFrac.FracColoring.card_le_indepNum_mul_total
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:48:16.203671+00:00
-- url     : https://prove2.me/submissions/15b06079-8ab1-41a3-a321-2e760b857050

import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
open GeomFrac FracColoring Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (c : FracColoring G) : (Fintype.card V : ℝ) ≤ (G.indepNum : ℝ) * c.total := by
  classical
  have hdual : ∀ c : FracColoring G, (Fintype.card V : ℝ) ≤ (G.indepNum : ℝ) * c.total := by
    intro c
    have hcount : ∑ v : V, ∑ S ∈ Finset.univ.filter (fun S : Finset V => v ∈ S), c.weight S
        = ∑ S : Finset V, (S.card : ℝ) * c.weight S := by
      have hinner : ∀ S : Finset V,
          (∑ _v ∈ S, c.weight S) = (S.card : ℝ) * c.weight S := by
        intro S
        rw [Finset.sum_const, nsmul_eq_mul]
      calc ∑ v : V, ∑ S ∈ Finset.univ.filter (fun S : Finset V => v ∈ S), c.weight S
          = ∑ v : V, ∑ S : Finset V, (if v ∈ S then c.weight S else 0) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.sum_filter]
        _ = ∑ S : Finset V, ∑ v : V, (if v ∈ S then c.weight S else 0) := Finset.sum_comm
        _ = ∑ S : Finset V, (S.card : ℝ) * c.weight S := by
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [Finset.sum_ite_mem, Finset.univ_inter, hinner S]
    have hstep : ∀ S : Finset V, (S.card : ℝ) * c.weight S ≤ (G.indepNum : ℝ) * c.weight S := by
      intro S
      by_cases hw : c.weight S = 0
      · rw [hw]; simp
      · have hindep : G.IsIndepSet (S : Set V) := by
          by_contra hc
          exact hw (c.supp S hc)
        have hcard : (S.card : ℝ) ≤ (G.indepNum : ℝ) := by
          exact_mod_cast SimpleGraph.IsIndepSet.card_le_indepNum hindep
        exact mul_le_mul_of_nonneg_right hcard (c.nonneg S)
    calc (Fintype.card V : ℝ) = ∑ _v : V, (1 : ℝ) := by simp
      _ ≤ ∑ v : V, ∑ S ∈ Finset.univ.filter (fun S : Finset V => v ∈ S), c.weight S :=
          Finset.sum_le_sum fun v _ => c.covers v
      _ = ∑ S : Finset V, (S.card : ℝ) * c.weight S := hcount
      _ ≤ ∑ S : Finset V, (G.indepNum : ℝ) * c.weight S := Finset.sum_le_sum fun S _ => hstep S
      _ = (G.indepNum : ℝ) * c.total := by rw [← Finset.mul_sum]; rfl
  exact hdual c

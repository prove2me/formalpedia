-- Prove2me | solution 2 for GeomFrac.geomFrac_ge_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:44:03.35303+00:00
-- url     : https://prove2.me/submissions/e55fa9b8-8f05-4c24-84e5-e6b1c2006336

import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
open GeomFrac FracColoring Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hα : 0 < G.indepNum) : (Fintype.card V : ℝ) / (G.indepNum : ℝ) ≤ geomFrac G := by
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
  -- the LP is feasible: the library's singleton colouring
  have hne : (Set.range (fun c : FracColoring G => c.total)).Nonempty :=
    ⟨(FracColoring.singleton G).total, Set.mem_range_self _⟩
  refine le_csInf hne ?_
  rintro x ⟨c, rfl⟩
  have hαR : (0 : ℝ) < (G.indepNum : ℝ) := by exact_mod_cast hα
  rw [div_le_iff₀ hαR]
  calc (Fintype.card V : ℝ) ≤ (G.indepNum : ℝ) * c.total := hdual c
    _ = c.total * (G.indepNum : ℝ) := by ring

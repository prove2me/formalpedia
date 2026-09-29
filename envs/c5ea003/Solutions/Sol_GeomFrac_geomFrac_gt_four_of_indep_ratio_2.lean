-- Prove2me | solution 2 for GeomFrac.geomFrac_gt_four_of_indep_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:32:08.552999+00:00
-- url     : https://prove2.me/submissions/165dfa2c-9ff5-41d8-89e6-70963a9bc638

import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
open GeomFrac FracColoring Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : 4 * G.indepNum < Fintype.card V) : 4 < geomFrac G := by
  classical
  -- `V` is nonempty and has an independent singleton, so `indepNum ≥ 1`
  have hcardpos : 0 < Fintype.card V := by omega
  obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hcardpos
  have hsingle : ∀ v : V, G.IsIndepSet (({v} : Finset V) : Set V) := by
    intro v
    simpa using Set.pairwise_singleton v fun a b => ¬G.Adj a b
  have hα : 0 < G.indepNum := by
    have := SimpleGraph.IsIndepSet.card_le_indepNum (hsingle v₀)
    simpa using this
  -- WEAK DUALITY: every fractional colouring costs at least `card V / indepNum`
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
  -- FEASIBILITY: the library's singleton colouring witnesses the LP
  have hne : (Set.range (fun c : FracColoring G => c.total)).Nonempty :=
    ⟨(FracColoring.singleton G).total, Set.mem_range_self _⟩
  -- conclude through the infimum
  have hratio : (Fintype.card V : ℝ) / (G.indepNum : ℝ) ≤ geomFrac G := by
    refine le_csInf hne ?_
    rintro x ⟨c, rfl⟩
    have hαR : (0 : ℝ) < (G.indepNum : ℝ) := by exact_mod_cast hα
    rw [div_le_iff₀ hαR]
    calc (Fintype.card V : ℝ) ≤ (G.indepNum : ℝ) * c.total := hdual c
      _ = c.total * (G.indepNum : ℝ) := by ring
  have hαR : (0 : ℝ) < (G.indepNum : ℝ) := by exact_mod_cast hα
  have h4 : (4 : ℝ) < (Fintype.card V : ℝ) / (G.indepNum : ℝ) := by
    rw [lt_div_iff₀ hαR]
    have : (4 : ℝ) * (G.indepNum : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast h
    linarith
  linarith

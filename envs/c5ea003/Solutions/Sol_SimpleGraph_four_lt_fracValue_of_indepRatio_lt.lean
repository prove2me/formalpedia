-- Prove2me | solution 1 for SimpleGraph.four_lt_fracValue_of_indepRatio_lt
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:02:17.807592+00:00
-- url     : https://prove2.me/submissions/c25ba694-6a03-462b-91b5-50635d986f92

import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

private theorem quick_value_ge_of_indepNum (F : G.FracColoring) (hα : 0 < G.indepNum) :
    (Fintype.card V : ℚ) / (G.indepNum : ℚ) ≤ F.value := by
  classical
  rw [ div_le_iff₀ ( Nat.cast_pos.mpr hα ) ];
  have h_double_count : ∑ v : V, ∑ s ∈ (Finset.univ : Finset V).powerset, (if v ∈ s then F.w s else 0) ≤ ∑ s ∈ (Finset.univ : Finset V).powerset, (G.indepNum : ℚ) * F.w s := by
    rw [ Finset.sum_comm ];
    gcongr;
    by_cases h : F.w ‹_› = 0 <;> simp_all +decide;
    exact mul_le_mul_of_nonneg_right ( mod_cast F.supp_indep _ h |> fun h => h.card_le_indepNum ) ( F.nonneg _ );
  convert h_double_count.trans' _ using 1;
  · rw [ ← Finset.mul_sum _ _ _, mul_comm, FracColoring.value ];
  · exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun v _ => F.covers v )


theorem solution (hpos : 0 < Fintype.card V)
    (hα : 0 < G.indepNum) (h : G.indepRatio < 1 / 4) (F : G.FracColoring) :
    4 < F.value := by
  classical
  have hn : (0 : ℚ) < (Fintype.card V : ℚ) := Nat.cast_pos.mpr hpos
  have ha : (0 : ℚ) < (G.indepNum : ℚ) := Nat.cast_pos.mpr hα
  have hs : (4 : ℚ) * (G.indepNum : ℚ) < (Fintype.card V : ℚ) := by
    rw [SimpleGraph.indepRatio, div_lt_iff₀ hn] at h
    linarith
  refine lt_of_lt_of_le ?_ (quick_value_ge_of_indepNum G F hα)
  exact (lt_div_iff₀ ha).2 (by linarith)

#print axioms solution

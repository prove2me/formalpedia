-- Prove2me | solution 1 for GoldbachActiveRoundedData.all_distinguished_objectives_lt_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:34:36.359986+00:00
-- url     : https://prove2.me/submissions/36c0c02e-0f94-4079-a402-47cbf71dc28e

import Definitions.Def_GoldbachActiveRoundedData
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped BigOperators
set_option autoImplicit false

open GoldbachActiveRoundedData

private theorem all_integer_ceilings : ∀ k : Fin 3,
    200000*(((distinguished k).exponential+(distinguished k).firstCap)^2+
      (distinguished k).restCap*(distinguished k).restMass) < 198479*scale^2 := by
  decide +kernel

theorem solution (k : Fin 3) (e f : ℝ) (u : ℕ → ℝ)
    (he0 : 0 ≤ e) (hf0 : 0 ≤ f) (hu0 : ∀ i, 0 ≤ u i)
    (he : e ≤ ((GoldbachActiveRoundedData.distinguished k).exponential:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (hf : f ≤ ((GoldbachActiveRoundedData.distinguished k).firstCap:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (hu : ∀ i, u i ≤ ((GoldbachActiveRoundedData.distinguished k).restCap:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ))
    (hmass : ∀ n, (∑ i ∈ Finset.range n, u i) ≤
      ((GoldbachActiveRoundedData.distinguished k).restMass:ℝ)/
      (GoldbachActiveRoundedData.scale:ℝ)) :
    Summable (fun i => (u i)^2) ∧
    (e+f)^2+(∑' i, (u i)^2) < (198479:ℝ)/200000 := by
  have hD : 0 < (scale:ℝ) := by norm_num [scale]
  let C : ℝ := ((distinguished k).restCap:ℝ)/(scale:ℝ)
  let V : ℝ := ((distinguished k).restMass:ℝ)/(scale:ℝ)
  have hC : 0 ≤ C := div_nonneg (Nat.cast_nonneg _) hD.le
  have hpartial : ∀ n, (∑ i ∈ Finset.range n, (u i)^2) ≤ C*V := by
    intro n
    calc
      _ ≤ ∑ i ∈ Finset.range n, C*u i := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hu i
        change u i ≤ C at hi
        nlinarith [mul_nonneg (hu0 i) (sub_nonneg.mpr hi)]
      _ = C*(∑ i ∈ Finset.range n, u i) := by rw [Finset.mul_sum]
      _ ≤ C*V := mul_le_mul_of_nonneg_left (hmass n) hC
  have hs := summable_of_sum_range_le (fun i => sq_nonneg (u i)) hpartial
  have ht : (∑' i, (u i)^2) ≤ C*V :=
    Real.tsum_le_of_sum_range_le (fun i => sq_nonneg (u i)) hpartial
  have hsq : (e+f)^2 ≤
      (((distinguished k).exponential:ℝ)/(scale:ℝ)+
       ((distinguished k).firstCap:ℝ)/(scale:ℝ))^2 := by
    have h := mul_self_le_mul_self (add_nonneg he0 hf0) (add_le_add he hf)
    simpa only [pow_two] using h
  refine ⟨hs,lt_of_le_of_lt (add_le_add hsq ht) ?_⟩
  dsimp [C,V]
  rw [← add_div,div_pow,← mul_div_mul_comm,← pow_two,← add_div]
  apply (div_lt_iff₀ (sq_pos_of_pos hD)).mpr
  have h : (200000:ℝ)*
      ((((distinguished k).exponential:ℝ)+((distinguished k).firstCap:ℝ))^2+
        ((distinguished k).restCap:ℝ)*((distinguished k).restMass:ℝ)) <
      (198479:ℝ)*(scale:ℝ)^2 := by
    exact_mod_cast all_integer_ceilings k
  nlinarith

#print axioms solution

-- Prove2me | solution 1 for markov_polya_grid_v2
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:21:49.791033+00:00
-- url     : https://prove2.me/submissions/24449cea-2a9e-47c4-b5d3-eb5dc9c5df45

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Polynomial

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

private noncomputable def witness : Polynomial ℝ :=
  C (1 / 17420181261730140817797573414006060306035097600000) *
    (-C 9971411306782352126547538802203688304818936064000 * X +
      C 1805670176749440845004197153469585983723594544000 * X ^ 2 -
      C 113674936632661253038168342523813961822677608320 * X ^ 3 +
      C 3568868446157488858790641933079905994849308824 * X ^ 4 -
      C 65099128971846497919183024886235137843526140 * X ^ 5 +
      C 746673854613436394084075214984302022773566 * X ^ 6 -
      C 5610452107537779326103033449915646183609 * X ^ 7 +
      C 28034844341127376477087258158558865269 * X ^ 8 -
      C 92332003101575728196449781732078442 * X ^ 9 +
      C 192554124114635494179078480984108 * X ^ 10 -
      C 230427350834140577504889659489 * X ^ 11 +
      C 120540902539766429535636233 * X ^ 12)

private theorem witness_degree : witness.natDegree ≤ 12 := by
  unfold witness
  compute_degree

private theorem witness_zero : witness.eval 0 = 0 := by
  norm_num [witness]

private def gridInteger (t : ℕ) : ℤ :=
  -9971411306782352126547538802203688304818936064000 * t +
    1805670176749440845004197153469585983723594544000 * t ^ 2 -
    113674936632661253038168342523813961822677608320 * t ^ 3 +
    3568868446157488858790641933079905994849308824 * t ^ 4 -
    65099128971846497919183024886235137843526140 * t ^ 5 +
    746673854613436394084075214984302022773566 * t ^ 6 -
    5610452107537779326103033449915646183609 * t ^ 7 +
    28034844341127376477087258158558865269 * t ^ 8 -
    92332003101575728196449781732078442 * t ^ 9 +
    192554124114635494179078480984108 * t ^ 10 -
    230427350834140577504889659489 * t ^ 11 +
    120540902539766429535636233 * t ^ 12

private theorem gridInteger_bounds : ∀ t : Fin 321,
    -(17420181261730140817797573414006060306035097600000 : ℤ) ≤ gridInteger t ∧
      gridInteger t ≤ 17420181261730140817797573414006060306035097600000 := by decide

private theorem witness_integer (t : ℕ) : witness.eval (t : ℝ) =
    (gridInteger t : ℝ) / 17420181261730140817797573414006060306035097600000 := by
  simp only [witness, eval_mul, eval_add, eval_sub, eval_neg, eval_C, eval_pow, eval_X]
  unfold gridInteger
  push_cast
  ring

private theorem witness_grid (t : ℕ) (ht : t ≤ 320) :
    |witness.eval (t : ℝ)| ≤ 1 := by
  have hi := gridInteger_bounds ⟨t, Nat.lt_succ_of_le ht⟩
  have hr : -(17420181261730140817797573414006060306035097600000 : ℝ) ≤
        (gridInteger t : ℝ) ∧
      (gridInteger t : ℝ) ≤ 17420181261730140817797573414006060306035097600000 := by
    exact_mod_cast hi
  have hd : (0 : ℝ) < 17420181261730140817797573414006060306035097600000 := by norm_num
  rw [witness_integer]
  exact abs_le.mpr ⟨(le_div_iff₀ hd).2 (by simpa using hr.1),
    (div_le_iff₀ hd).2 (by simpa using hr.2)⟩

private def derivativeInteger (t : ℕ) : ℤ :=
  -9971411306782352126547538802203688304818936064000 +
    2 * 1805670176749440845004197153469585983723594544000 * t -
    3 * 113674936632661253038168342523813961822677608320 * t ^ 2 +
    4 * 3568868446157488858790641933079905994849308824 * t ^ 3 -
    5 * 65099128971846497919183024886235137843526140 * t ^ 4 +
    6 * 746673854613436394084075214984302022773566 * t ^ 5 -
    7 * 5610452107537779326103033449915646183609 * t ^ 6 +
    8 * 28034844341127376477087258158558865269 * t ^ 7 -
    9 * 92332003101575728196449781732078442 * t ^ 8 +
    10 * 192554124114635494179078480984108 * t ^ 9 -
    11 * 230427350834140577504889659489 * t ^ 10 +
    12 * 120540902539766429535636233 * t ^ 11

private theorem witness_derivative_integer (t : ℕ) : witness.derivative.eval (t : ℝ) =
    (derivativeInteger t : ℝ) / 17420181261730140817797573414006060306035097600000 := by
  simp only [witness, derivative_mul, derivative_add, derivative_sub, derivative_neg,
    derivative_C, derivative_X, derivative_X_pow, eval_mul, eval_add, eval_sub,
    eval_neg, eval_C, eval_pow, eval_X, eval_zero, eval_one]
  unfold derivativeInteger
  push_cast
  ring

private theorem derivativeInteger_value : derivativeInteger 320 =
    15678764713895392913504843311775724971331198720000 := by decide

private theorem witness_derivative :
    witness.derivative.eval 320 =
      312777602295227347957506257700196313 /
        347517334816773659433743013107135040 := by
  rw [show (320 : ℝ) = ((320 : ℕ) : ℝ) from rfl, witness_derivative_integer,
    derivativeInteger_value]
  norm_num

theorem solution : ¬ (∀ {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ},
    Q.natDegree ≤ d → Q.eval 0 = 0 →
    (∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1) →
    2 * d ^ 2 ≤ b → ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ) ^ 2 / (b : ℝ)) := by
  intro h
  have hbad := @h 320 (by norm_num) witness 12 witness_degree witness_zero
    witness_grid (by norm_num) 320 (by norm_num) (by norm_num)
  rw [witness_derivative] at hbad
  norm_num at hbad

#print axioms solution

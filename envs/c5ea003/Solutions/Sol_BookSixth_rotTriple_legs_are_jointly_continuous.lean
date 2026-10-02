-- Prove2me | solution 1 for BookSixth.rotTriple_legs_are_jointly_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T01:50:01.277801+00:00
-- url     : https://prove2.me/submissions/7b8e13dc-47e4-418e-9a01-54170fe78201

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
open scoped BigOperators
open scoped Matrix
open BookSixth Matrix

noncomputable section


def rotM (t θ1 θ2 θ3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1)

lemma continuous_rotM (θ1 θ2 θ3 : ℝ) : Continuous fun t : ℝ => rotM t θ1 θ2 θ3 := by
  unfold rotM rot12Matrix rot02Matrix rot01Matrix
  fun_prop

lemma cont_forward_leg (θ1 θ2 θ3 : ℝ) (a : Fin 3 → ℝ) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) =>
      rotM p.1 θ1 θ2 θ3 *ᵥ p.2 + p.1 • a := by
  unfold rotM
  simp only [← Matrix.mulVec_mulVec, add_smul, Pi.add_apply, Pi.smul_apply,
    add_assoc]
  unfold rot12Matrix rot02Matrix rot01Matrix
  fun_prop

lemma cont_inverse_leg (θ1 θ2 θ3 : ℝ) (a : Fin 3 → ℝ) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) =>
      (rotM p.1 θ1 θ2 θ3)ᵀ *ᵥ p.2 - p.1 • ((rotM p.1 θ1 θ2 θ3)ᵀ *ᵥ a) := by
  have _hc : Continuous fun t : ℝ => rotM t θ1 θ2 θ3 := continuous_rotM θ1 θ2 θ3
  fun_prop

-- Joint continuity of the two legs of the isotopy.  The forward leg is
-- `R(t) *v x + t a`; the inverse leg is the transpose rotation applied to
-- `x - t a`, which by linearity is `R(t)^T *v x - t (R(t)^T *v a)`.

theorem solution (θ1 θ2 θ3 : ℝ) (a : Fin 3 → ℝ) :
    (Continuous fun p : ℝ × (Fin 3 → ℝ) =>
      rotTriple p.1 θ1 θ2 θ3 p.2 + p.1 • a) ∧
    (Continuous fun p : ℝ × (Fin 3 → ℝ) =>
      (rot12Matrix (p.1 * θ3) * rot02Matrix (p.1 * θ2)
          * rot01Matrix (p.1 * θ1))ᵀ *ᵥ p.2
        - p.1 • ((rot12Matrix (p.1 * θ3) * rot02Matrix (p.1 * θ2)
            * rot01Matrix (p.1 * θ1))ᵀ *ᵥ a)) := by
  constructor
  · -- the forward leg
    rw [show (fun p : ℝ × (Fin 3 → ℝ) => rotTriple p.1 θ1 θ2 θ3 p.2 + p.1 • a)
        = (fun p => rotM p.1 θ1 θ2 θ3 *ᵥ p.2 + p.1 • a) by
      funext p; unfold rotM rotTriple
      simp only [rot12CLM, rot02CLM, rot01CLM]
      simp; simp only [Matrix.mul_assoc]]
    exact cont_forward_leg θ1 θ2 θ3 a
  · -- the inverse leg
    rw [show (fun p : ℝ × (Fin 3 → ℝ) =>
        (rot12Matrix (p.1 * θ3) * rot02Matrix (p.1 * θ2)
          * rot01Matrix (p.1 * θ1))ᵀ *ᵥ p.2
          - p.1 • ((rot12Matrix (p.1 * θ3) * rot02Matrix (p.1 * θ2)
              * rot01Matrix (p.1 * θ1))ᵀ *ᵥ a))
        = (fun p => (rotM p.1 θ1 θ2 θ3)ᵀ *ᵥ p.2
          - p.1 • ((rotM p.1 θ1 θ2 θ3)ᵀ *ᵥ a)) by
      funext p; rfl]
    exact cont_inverse_leg θ1 θ2 θ3 a

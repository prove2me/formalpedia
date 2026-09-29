-- Prove2me | solution 1 for LinearOptimization.integer_program_weak_lagrangean_duality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T02:55:16.185498+00:00
-- url     : https://prove2.me/submissions/64dfc1da-ee9b-43ed-8b6c-38bc90124de8

import Definitions.Def_LinearOptimization_IntegerProgram
import Definitions.Def_LinearOptimization_LagrangeanDual
import Mathlib.Tactic

open Matrix
open LinearOptimization

/-- Bertsimas--Tsitsiklis, Theorem 11.2, p. 495. -/
theorem solution {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℤ) (b : Fin m₁ → ℤ) (c : Fin n → ℤ)
    (D : Matrix (Fin m₂) (Fin n) ℤ) (d : Fin m₂ → ℤ) :
    lagrangeanDualValue (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))
        (fun j => (c j : ℝ))
        (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))) ≤
      integerProgramValue (fun j => (c j : ℝ)) (A.map ((↑) : ℤ → ℝ))
        (fun i => (b i : ℝ)) (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)) := by
  let Ar := A.map ((↑) : ℤ → ℝ)
  let br : Fin m₁ → ℝ := fun i => (b i : ℝ)
  let cr : Fin n → ℝ := fun j => (c j : ℝ)
  let Dr := D.map ((↑) : ℤ → ℝ)
  let dr : Fin m₂ → ℝ := fun i => (d i : ℝ)
  unfold lagrangeanDualValue integerProgramValue lpValue
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  have hxA : br ≤ Ar.mulVec x := hx.1
  have hxX : x ∈ lagrangeanIntegerSet Dr dr := ⟨hx.2.1, hx.2.2⟩
  have hobj : lagrangeanObjective Ar br cr (lagrangeanIntegerSet Dr dr) p ≤
      ((cr ⬝ᵥ x + p ⬝ᵥ (br - Ar.mulVec x) : ℝ) : EReal) := by
    unfold lagrangeanObjective
    exact iInf_le_of_le x (iInf_le_of_le hxX le_rfl)
  apply hobj.trans
  norm_cast
  have hdiff : br - Ar.mulVec x ≤ 0 := sub_nonpos.mpr hxA
  have hpen : p ⬝ᵥ (br - Ar.mulVec x) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hp i) (hdiff i)
  linarith

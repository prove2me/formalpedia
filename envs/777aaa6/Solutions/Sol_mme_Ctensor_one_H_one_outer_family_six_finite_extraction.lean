-- Prove2me | solution 1 for mme_Ctensor_one_H_one_outer_family_six_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:40:56.920429+00:00
-- url     : https://prove2.me/submissions/91b655e8-b9a0-4186-a791-447c5f834a87

import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_finite_MM_extraction_swap_double_uniform

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hH : 0 < H) :
    let lower : ℝ :=
      (A : ℝ) ^ 3 *
        ((H : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt
            (Real.log (((H + 1 : ℕ) : ℝ)))))
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization T) ∧
      lower ^ (2 : ℕ) ≤ (q : ℝ) ∧
      (∀ j, a j * b j * c j = volume ^ 6) := by
  dsimp only
  obtain ⟨k, a, b, c, hrestrict, hcount, hvolume⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction stars hH
  let lower : ℝ :=
    (A : ℝ) ^ 3 *
      ((H : ℝ) ^ 2 *
        Real.exp (-100 * Real.sqrt
          (Real.log (((H + 1 : ℕ) : ℝ)))))
  have hlower : 0 ≤ lower := by
    dsimp only [lower]
    positivity
  obtain ⟨q, a', b', c', hrestrict', hcount', hvolume'⟩ :=
    mme_finite_MM_extraction_swap_double_uniform
      a b c lower hlower hcount hrestrict hvolume
  refine ⟨q, a', b', c', hrestrict', ?_, ?_⟩
  · exact hcount'
  · intro j
    rw [hvolume' j]
    norm_num [← pow_mul]


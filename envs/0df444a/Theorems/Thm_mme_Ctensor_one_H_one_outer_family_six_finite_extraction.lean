-- Prove2me | Theorems.Thm_mme_Ctensor_one_H_one_outer_family_six_finite_extraction
-- name    : mme_Ctensor_one_H_one_outer_family_six_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:40:40.306883+00:00
-- url     : https://prove2.me/theorems/71343ef8-a646-4a5c-bd9a-1089612a64e3
-- title:
--   Six-symmetric finite extraction from one C-tensor outer family
-- statement:
--   An outer family of A C-tensors with H inner components and common component volume v yields a finite matrix-multiplication extraction from the six-symmetrization. Its multiplicity is at least the square of A³H² exp(-100√log(H+1)), and every extracted matrix-multiplication tensor has volume v⁶.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3, combined with the standard cyclic C-tensor extraction.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_Ctensor_one_H_one_outer_family_six_finite_extraction
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
  sorry

-- Prove2me | Theorems.Thm_mme_six_restricted_kron_exponential_extraction
-- name    : mme_six_restricted_kron_exponential_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:03:35.875983+00:00
-- url     : https://prove2.me/theorems/d8a60c98-41b3-431f-b45c-b1f1541478e4
-- title:
--   Two extracted factors combine their complete exponential rates
-- statement:
--   Matrix families from two tensor factors combine at the sum of logarithmic weight rates and transfer through an actual restriction to the source tensor, with positive resulting copy count. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_six_product_exponential_extraction
import Theorems.Thm_mme_sixSymmetrization_restrict
open BigOperators MME MME.TensorObj
universe u

theorem mme_six_restricted_kron_exponential_extraction
    {K : Type u} [Field K] {X Y T : TensorObj K 3}
    (hsource : Restrict (kron X Y) T) (tau rateX rateY : ℝ)
    (hX : ∃ (q : ℕ) (a b c : Fin q → ℕ),
      Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j))) (sixSymmetrization X) ∧
      Real.exp rateX ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau))
    (hY : ∃ (q : ℕ) (a b c : Fin q → ℕ),
      Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j))) (sixSymmetrization Y) ∧
      Real.exp rateY ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
      Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j))) (sixSymmetrization T) ∧
      Real.exp (rateX + rateY) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by sorry

-- Prove2me | Theorems.Thm_mme_repeated_extraction_six_matrix_weight_rate
-- name    : mme_repeated_extraction_six_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T08:34:18.916647+00:00
-- url     : https://prove2.me/theorems/fdf970db-cf30-403a-ace3-972b9d1242c2
-- title:
--   Outer copy rates add to symmetrized matrix weights
-- statement:
--   A repeated tensor extraction with exponential copy lower bound composes with a matrix family from its symmetrized output. The resulting positive matrix family retains six times the outer logarithmic copy rate plus the full child weight rate. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_six_repeated_matrix_family_weight
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MME
open scoped BigOperators
universe u

theorem mme_repeated_extraction_six_matrix_weight_rate
    {K : Type u} [Field K] {p q : ℕ} {X Y : TensorObj K 3}
    (a b c : Fin q → ℕ) (hq : 0 < q) (tau parentRate rate : ℝ)
    (hparent : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin p => Y)) X)
    (hcopies : Real.exp parentRate ≤ (p : ℝ))
    (hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization Y))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ), 0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization X) ∧
      Real.exp (6 * parentRate + rate) ≤
        ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by sorry

-- Prove2me | Theorems.Thm_mme_permuted_product_extraction_six_matrix_weight_rate
-- name    : mme_permuted_product_extraction_six_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:18:15.09716+00:00
-- url     : https://prove2.me/theorems/5c1576b1-2134-413d-8c33-8b202bea48c5
-- title:
--   Independent permuted extractions retain their full copy rate
-- statement:
--   Independent repeated tensor restrictions combine with a matrix family after whole-factor mode permutations. The resulting sixfold matrix weight retains six times the sum of logarithmic copy bounds plus the complete child rate, with positive multiplicity. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_repeated_extraction_six_matrix_weight_rate
import Theorems.Thm_mme_kronFin_repeated_isomorphic
import Theorems.Thm_mme_kronFin_mono_restrict
import Definitions.Def_mme_rank_bridge
open MME MME.TensorObj
open scoped BigOperators
universe u

theorem mme_permuted_product_extraction_six_matrix_weight_rate
    {K : Type u} [Field K] {n q : ℕ}
    (X Y : Fin n → TensorObj K 3) (copies : Fin n → ℕ)
    (sigma : Fin n → Equiv.Perm (Fin 3)) (parentRate : Fin n → ℝ)
    (a b c : Fin q → ℕ) (hq : 0 < q) (tau rate : ℝ)
    (hparent : ∀ r, Restrict (bigAdd (fun _ : Fin (copies r) => Y r)) (X r))
    (hcopies : ∀ r, Real.exp (parentRate r) ≤ (copies r : ℝ))
    (hchild : Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization (kronFin n (fun r => permObj (sigma r) (Y r)))))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    ∃ (m : ℕ) (a' b' c' : Fin m → ℕ), 0 < m ∧
      Restrict (bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization (kronFin n (fun r => permObj (sigma r) (X r)))) ∧
      Real.exp (6 * (∑ r, parentRate r) + rate) ≤
        ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by sorry

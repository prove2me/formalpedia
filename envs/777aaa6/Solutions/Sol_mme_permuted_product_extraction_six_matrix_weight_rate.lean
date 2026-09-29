-- Prove2me | solution 1 for mme_permuted_product_extraction_six_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:25.044539+00:00
-- url     : https://prove2.me/submissions/6d67a224-545b-420d-bd02-6bc0aa35458f

import Theorems.Thm_mme_repeated_extraction_six_matrix_weight_rate
import Theorems.Thm_mme_kronFin_repeated_isomorphic
import Theorems.Thm_mme_kronFin_mono_restrict
import Definitions.Def_mme_rank_bridge

open MME MME.TensorObj
open scoped BigOperators
universe u

private theorem perm_repeated {K : Type u} [Field K]
    (sigma : Equiv.Perm (Fin 3)) (T : TensorObj K 3) (n : ℕ) :
    Isomorphic (permObj sigma (bigAdd (fun _ : Fin n => T)))
      (bigAdd (fun _ : Fin n => permObj sigma T)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [← TensorQ.permAut_toQ, TensorQ.toQ_bigAdd, map_sum, TensorQ.toQ_bigAdd]
  simp only [TensorQ.permAut_toQ]

/-- Independent extractions retain the sum of their logarithmic copy bounds
after whole-factor mode permutations and composition with a matrix family. -/
theorem solution
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
        ∑ j, ((a' j * b' j * c' j : ℕ) : ℝ) ^ tau := by
  have hproduct : Restrict
      (bigAdd (fun _ : Fin (∏ r, copies r) =>
        kronFin n (fun r => permObj (sigma r) (Y r))))
      (kronFin n (fun r => permObj (sigma r) (X r))) := by
    apply (mme_kronFin_repeated_isomorphic
      (fun r => permObj (sigma r) (Y r)) copies).2.trans
    apply mme_kronFin_mono_restrict
    intro r
    exact (perm_repeated (sigma r) (Y r) (copies r)).2.trans
      (permObj_restrict (sigma r) (hparent r))
  have hcount : Real.exp (∑ r, parentRate r) ≤ ((∏ r, copies r : ℕ) : ℝ) := by
    rw [Real.exp_sum, Nat.cast_prod]
    exact Finset.prod_le_prod (fun r _ => (Real.exp_pos _).le) (fun r _ => hcopies r)
  exact mme_repeated_extraction_six_matrix_weight_rate
    a b c hq tau (∑ r, parentRate r) rate hproduct hcount hchild hweight


#print axioms solution

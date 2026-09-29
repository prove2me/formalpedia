-- Prove2me | solution 1 for mme_six_repeated_matrix_family_weight
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:51:17.086916+00:00
-- url     : https://prove2.me/submissions/2b325c5f-f7e0-4780-bb26-d487c0752d25

import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators
universe u
set_option autoImplicit false

/-- Repeating a tensor before six-symmetrization gives the sixth power of
its multiplicity, with no loss of copies. -/
private theorem mme_sixSymmetrization_repeated_isomorphic
    {K : Type u} [Field K] (p : ℕ) (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun _ : Fin (p ^ 6) => sixSymmetrization T))
      (sixSymmetrization (TensorObj.bigAdd (fun _ : Fin p => T))) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.toQ_bigAdd, ← TensorQ.permAut_toQ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    map_mul, map_natCast, Nat.cast_pow]
  ring

/-- A child extraction composes with a repeated parent extraction while
retaining all sixth-power copies created by symmetrization. -/
private theorem mme_six_repeated_extraction_compose
    {K : Type u} [Field K] {p : ℕ} {X Y Z : TensorObj K 3}
    (hparent : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin p => Y)) X)
    (hchild : TensorObj.Restrict Z (sixSymmetrization Y)) :
    TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin (p ^ 6) => Z))
      (sixSymmetrization X) := by
  exact (mme_bigAdd_mono_restrict (fun _ => hchild)).trans
    ((mme_sixSymmetrization_repeated_isomorphic p Y).1.trans
      (mme_sixSymmetrization_restrict hparent))


private theorem repeated_sum {A : Type*} [AddCommMonoid A] (p q : ℕ) (f : Fin q → A) :
    (∑ r : Fin (p * q), f (finProdFinEquiv.symm r).2) = p • ∑ j, f j := by
  calc
    _ = ∑ ij : Fin p × Fin q, f ij.2 := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      intro ij
      rw [Equiv.symm_apply_apply]
    _ = _ := by simp [Fintype.sum_prod_type]

/-- Flattening the repeated child family retains the parent multiplicity
and multiplies the child's weight by its sixth power. -/
theorem solution
    {K : Type u} [Field K] {p q : ℕ} {X Y : TensorObj K 3}
    (a b c : Fin q → ℕ) (tau rate : ℝ)
    (hparent : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin p => Y)) X)
    (hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization Y))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun r : Fin (p ^ 6 * q) =>
        let j := (finProdFinEquiv.symm r).2
        MMObj K (a j) (b j) (c j))) (sixSymmetrization X) ∧
    (p : ℝ) ^ 6 * Real.exp rate ≤
      ∑ r : Fin (p ^ 6 * q),
        let j := (finProdFinEquiv.symm r).2
        ((a j * b j * c j : ℕ) : ℝ) ^ tau := by
  constructor
  · have hflatten : TensorObj.Isomorphic
        (TensorObj.bigAdd (fun r : Fin (p ^ 6 * q) =>
          let j := (finProdFinEquiv.symm r).2
          MMObj K (a j) (b j) (c j)))
        (TensorObj.bigAdd (fun _ : Fin (p ^ 6) =>
          TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))) := by
      rw [← TensorQ.toQ_eq_iff]
      simp only [TensorQ.toQ_bigAdd]
      rw [repeated_sum (p ^ 6) q (fun j => TensorQ.toQ (MMObj K (a j) (b j) (c j)))]
      simp
    exact hflatten.1.trans (mme_six_repeated_extraction_compose hparent hchild)
  · dsimp only
    rw [repeated_sum (p ^ 6) q (fun j => ((a j * b j * c j : ℕ) : ℝ) ^ tau),
      nsmul_eq_mul, Nat.cast_pow]
    exact mul_le_mul_of_nonneg_left hweight (by positivity)


#print axioms solution

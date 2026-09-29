-- Prove2me | Definitions.Def_mme_kronFin_rec_append_data
-- name    : mme_kronFin_rec_append_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T06:07:45.803457+00:00
-- url     : https://prove2.me/theorems/00426f64-c0ef-4ab0-a52a-bb518dbe4ae4
-- title:
--   Exact recursion-aligned concatenation data for heterogeneous Kronecker products
-- statement:
--   For two ordered heterogeneous tensor families, this module fixes a canonical flat concatenation whose recursion agrees definitionally with the right-associated finite Kronecker product. It supplies the corresponding modewise reassociation equivalence, the dependent split of every flat basis word into its left and right words, and the concatenated family of factor bases. The length is propositionally the ordinary sum of the two family lengths. These data retain coordinate-level semantics through the regrouping used in the DWZ Table-2 construction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (regrouping Table-2 component positions); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_mode_pi_basis

open MME TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.TensorObj

def recAppendLength : ℕ → ℕ → ℕ
  | 0, n => n
  | Nat.succ m, n => Nat.succ (recAppendLength m n)

theorem recAppendLength_eq_add : ∀ m n,
    recAppendLength m n = m + n
  | 0, n => by simp only [recAppendLength, Nat.zero_add]
  | Nat.succ m, n => by
      simp only [recAppendLength, recAppendLength_eq_add m n,
        Nat.succ_add]

private theorem recAppendLength_succ_pos (m n : ℕ) :
    0 < recAppendLength (Nat.succ m) n := by
  simp only [recAppendLength, Nat.zero_lt_succ]

def recAppendFamily {α : Type u} :
    ∀ (m n : ℕ), (Fin m → α) → (Fin n → α) →
      Fin (recAppendLength m n) → α
  | 0, _, _, B => B
  | Nat.succ m, n, A, B =>
      Fin.cons (A 0) (recAppendFamily m n (fun r ↦ A r.succ) B)

noncomputable def kronFinRecAppendModeEquiv
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (m n : ℕ) (A : Fin m → TensorObj K d)
      (B : Fin n → TensorObj K d) (i : Fin d),
      (TensorObj.kronFin (recAppendLength m n)
        (recAppendFamily m n A B)).V i ≃ₗ[K]
        (TensorObj.kron (TensorObj.kronFin m A)
          (TensorObj.kronFin n B)).V i
  | 0, n, _, B, i =>
      (TensorProduct.lid K ((TensorObj.kronFin n B).V i)).symm
  | Nat.succ m, n, A, B, i => by
      let Atail : Fin m → TensorObj K d := fun r ↦ A r.succ
      let E := kronFinRecAppendModeEquiv m n Atail B i
      exact
        (TensorProduct.congr (LinearEquiv.refl K ((A 0).V i)) E).trans
          (TensorProduct.assoc K ((A 0).V i)
            ((TensorObj.kronFin m Atail).V i)
            ((TensorObj.kronFin n B).V i)).symm

def recAppendLeftWord :
    ∀ {m n : ℕ}
      {indexA : Fin m → Type u} {indexB : Fin n → Type u},
      (∀ r, recAppendFamily m n indexA indexB r) →
        ∀ r, indexA r
  | 0, _, _, _, _ => fun r ↦ r.elim0
  | Nat.succ m, n, indexA, indexB, w =>
      Fin.cons (w ⟨0, recAppendLength_succ_pos m n⟩)
        (recAppendLeftWord
          (m := m) (n := n)
          (indexA := fun r ↦ indexA r.succ) (indexB := indexB)
          (fun r ↦ w r.succ))

def recAppendRightWord :
    ∀ {m n : ℕ}
      {indexA : Fin m → Type u} {indexB : Fin n → Type u},
      (∀ r, recAppendFamily m n indexA indexB r) →
        ∀ r, indexB r
  | 0, _, _, _, w => w
  | Nat.succ m, n, indexA, indexB, w =>
      recAppendRightWord
        (m := m) (n := n)
        (indexA := fun r ↦ indexA r.succ) (indexB := indexB)
        (fun r ↦ w r.succ)

noncomputable def recAppendBasisFamily
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (m n : ℕ) (A : Fin m → TensorObj K d)
      (B : Fin n → TensorObj K d) (i : Fin d)
      (indexA : Fin m → Type u) (indexB : Fin n → Type u),
      (∀ r, Basis (indexA r) K ((A r).V i)) →
      (∀ r, Basis (indexB r) K ((B r).V i)) →
      ∀ r, Basis (recAppendFamily m n indexA indexB r) K
        ((recAppendFamily m n A B r).V i)
  | 0, _, _, _, _, _, _, _, bB => bB
  | Nat.succ m, n, A, B, i, indexA, indexB, bA, bB =>
      Fin.cons (bA 0)
        (recAppendBasisFamily m n (fun r ↦ A r.succ) B i
          (fun r ↦ indexA r.succ) indexB (fun r ↦ bA r.succ) bB)

end MME.TensorObj



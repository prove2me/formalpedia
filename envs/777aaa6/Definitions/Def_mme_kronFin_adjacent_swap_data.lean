-- Prove2me | Definitions.Def_mme_kronFin_adjacent_swap_data
-- name    : mme_kronFin_adjacent_swap_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T19:39:22.868452+00:00
-- url     : https://prove2.me/theorems/0e1f781b-955f-49d2-8420-4b0b06baf02e
-- title:
--   Dependent adjacent-factor swap data for ordered Kronecker products
-- statement:
--   For a right-associated ordered product of heterogeneous tensor factors, define the exact family obtained by exchanging adjacent positions $j$ and $j+1$. The same recursion transports a dependent basis-index family, its factor bases, and words back to the original order. These data provide the coordinate interface for the symmetry isomorphism used when regrouping retained DWZ component words by their fifteen Table-2 rows.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (component-position regrouping); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_mode_pi_basis

open MME Module

universe u


namespace MME.TensorObj

set_option autoImplicit false
set_option warningAsError true

set_option linter.unusedVariables false in
/-- Exchange positions `j` and `j+1` in a finite dependent sequence, in a
recursive presentation aligned with the right-associated `kronFin`. -/
def finAdjacentSwapVector {α : Sort u} :
    ∀ {n : ℕ} (T : Fin (n + 2) → α)
      (j : Fin (n + 1)), Fin (n + 2) → α
  | 0, T, _ =>
      Fin.cases (T 1) (Fin.cases (T 0) (fun r ↦ T r.succ.succ))
  | n + 1, T, j =>
      Fin.cases
        (Fin.cases (T 1) (Fin.cases (T 0) (fun r ↦ T r.succ.succ)))
        (fun q => Fin.cons (T 0)
          (finAdjacentSwapVector (fun r : Fin (n + 2) ↦ T r.succ) q)) j

/-- The family of tensor factors with the adjacent positions exchanged. -/
def kronFinAdjacentSwapFamily
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    Fin (n + 2) → TensorObj K d :=
  finAdjacentSwapVector T j

/-- The dependent index family with the same adjacent positions exchanged. -/
def kronFinAdjacentSwapIndex {n : ℕ}
    (index : Fin (n + 2) → Type u) (j : Fin (n + 1)) :
    Fin (n + 2) → Type u :=
  finAdjacentSwapVector index j

/-- Restore a word over an adjacent-swapped dependent family to the original
factor order. -/
def kronFinAdjacentUnswapWord {n : ℕ}
    {index : Fin (n + 2) → Type u} :
    (j : Fin (n + 1)) →
      (∀ r, kronFinAdjacentSwapIndex index j r) → ∀ r, index r := by
  induction n with
  | zero =>
      exact fun _ w ↦
        Fin.cases (w 1) (Fin.cases (w 0) (fun r ↦ w r.succ.succ))
  | succ n ih =>
      exact fun j ↦ Fin.cases
        (fun w ↦ Fin.cases (w 1)
          (Fin.cases (w 0) (fun r ↦ w r.succ.succ)))
        (fun q w ↦ Fin.cons (w 0)
          (ih q (fun r : Fin (n + 2) ↦ w r.succ))) j

/-- Factor bases attached to an adjacent-swapped tensor family. -/
noncomputable def kronFinAdjacentSwapBasis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) (i : Fin d)
    {index : Fin (n + 2) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i)) :
    ∀ r, Basis (kronFinAdjacentSwapIndex index j r) K
      (((kronFinAdjacentSwapFamily T j) r).V i) := by
  induction n with
  | zero =>
      exact Fin.cases (b 1) (Fin.cases (b 0) (fun r ↦ b r.succ.succ))
  | succ n ih =>
      exact Fin.cases
        (Fin.cases (b 1) (Fin.cases (b 0) (fun r ↦ b r.succ.succ)))
        (fun q ↦ Fin.cons (b 0)
          (ih (fun r : Fin (n + 2) ↦ T r.succ) q
            (fun r : Fin (n + 2) ↦ b r.succ))) j

end MME.TensorObj



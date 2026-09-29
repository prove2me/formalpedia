-- Prove2me | solution 1 for HefferonLinAlg.jordanBlocks_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T14:33:43.072097+00:00
-- url     : https://prove2.me/submissions/0b956acb-125f-41ba-9288-9e2c9eacc794

import Definitions.Def_HefferonLinAlg_jordan
import Theorems.Thm_HefferonLinAlg_jordanBlock_count_from_kernel_dims

open Matrix
open HefferonLinAlg

private theorem count_eq_card {k : ℕ} (sz : Fin k → ℕ) (lam : Fin k → ℂ)
    (m : ℕ) (mu : ℂ) :
    Multiset.count (m, mu) (jordanBlocks sz lam)
      = (Finset.univ.filter fun i => sz i = m ∧ lam i = mu).card := by
  classical
  rw [jordanBlocks, Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro i _
  simp only [Prod.ext_iff, eq_comm]

theorem solution
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {k₁ k₂ : ℕ}
    {sz₁ : Fin k₁ → ℕ} {lam₁ : Fin k₁ → ℂ}
    {sz₂ : Fin k₂ → ℕ} {lam₂ : Fin k₂ → ℂ}
    (h₁ : IsJordanFormOf A sz₁ lam₁) (h₂ : IsJordanFormOf A sz₂ lam₂) :
    jordanBlocks sz₁ lam₁ = jordanBlocks sz₂ lam₂ := by
  classical
  rw [Multiset.ext]
  rintro ⟨m, mu⟩
  rw [count_eq_card, count_eq_card]
  cases m with
  | zero =>
      have z : ∀ {k : ℕ} (sz : Fin k → ℕ) (lam : Fin k → ℂ), (∀ i, 0 < sz i) →
          (Finset.univ.filter fun i => sz i = 0 ∧ lam i = mu).card = 0 := by
        intro k sz lam hpos
        simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hc
        exact absurd hc.1 (Nat.pos_iff_ne_zero.mp (hpos i))
      rw [z sz₁ lam₁ h₁.1, z sz₂ lam₂ h₂.1]
  | succ r =>
      have c₁ := HefferonLinAlg.jordanBlock_count_from_kernel_dims h₁ mu r
      have c₂ := HefferonLinAlg.jordanBlock_count_from_kernel_dims h₂ mu r
      omega

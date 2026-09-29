-- Prove2me | Theorems.Thm_rota_basis_conjecture
-- name    : rota_basis_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T20:41:45.605674+00:00
-- url     : https://prove2.me/theorems/12fe52f7-88a6-4276-b888-1ad4e56638a7
-- statement:
--   Rota's basis conjecture (1989): Given n bases B₁,...,Bₙ of an n-dimensional vector space V, there exists a system of distinct representatives (one from each basis) forming a basis. Proved for n ≤ 3 and special cases; general n is open.
-- source:
--   https://en.wikipedia.org/wiki/Rota%27s_basis_conjecture

import Mathlib

import Mathlib

theorem rota_basis_conjecture (n : ℕ) (hn : 1 ≤ n)
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (hdim : Module.finrank ℝ V = n)
    (bases : Fin n → Fin n → V)
    (hbases : ∀ i : Fin n, LinearIndependent ℝ (bases i)) :
    ∃ sigma : Fin n → Fin n,
      Function.Injective sigma ∧
      LinearIndependent ℝ (fun i => bases i (sigma i)) := by
  sorry

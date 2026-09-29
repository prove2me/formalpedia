-- Prove2me | Theorems.Thm_mme_finset_weighted_collision_averaging_isolated
-- name    : mme_finset_weighted_collision_averaging_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:57:20.946486+00:00
-- url     : https://prove2.me/theorems/1753cc1d-14ce-4792-b7b5-148616196676
-- title:
--   Weighted collision averaging selects one isolated state with aggregate mass
-- statement:
--   Let a finite random-state space retain an ambient edge family in each state. Each retained target edge carries a nonnegative integer mass at most $H$. Charge every directed target–ambient collision (sharing either distinguished coordinate) the full cost $H$. If the total mass over all states is at least the desired average lower bound plus this collision charge, then one state contains an isolated retained target subfamily whose aggregate mass meets that lower bound. This is the source-faithful aggregate quantifier needed to combine DWZ Claim 6.8 with first-hash collision pruning; it deliberately does not claim that one state is individually good for every owner.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21), Claim 6.8, and Corollary 5.11; https://arxiv.org/abs/2210.10173

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_finset_weighted_collision_averaging_isolated
    {State Edge X Y : Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (target : Finset Edge) (ambient : State → Finset Edge)
    (x : Edge → X) (y : Edge → Y)
    (mass : State → Edge → ℕ) (cap : ℕ) (lower : ℝ)
    (hmass : ∀ q a, a ∈ target → a ∈ ambient q → mass q a ≤ cap)
    (hbudget :
      (Fintype.card State : ℝ) * lower +
          ∑ q, ((cap *
            (((target.filter (fun a ↦ a ∈ ambient q)).product
              (ambient q)).filter (fun pair ↦
                pair.1 ≠ pair.2 ∧
                  (x pair.1 = x pair.2 ∨ y pair.1 = y pair.2))).card : ℕ) : ℝ) ≤
        ∑ q, (((∑ a ∈ target.filter (fun a ↦ a ∈ ambient q),
          mass q a) : ℕ) : ℝ)) :
    ∃ q : State, ∃ isolated : Finset Edge,
      isolated ⊆ target ∧
      isolated ⊆ ambient q ∧
      (∀ e ∈ isolated, ∀ e' ∈ ambient q,
        x e = x e' ∨ y e = y e' → e = e') ∧
      lower ≤ ((∑ a ∈ isolated, mass q a : ℕ) : ℝ) := by
  sorry

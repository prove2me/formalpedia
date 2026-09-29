-- Prove2me | Theorems.Thm_mme_dwz_claim6_8_exists_seven_eighths_nonholes
-- name    : mme_dwz_claim6_8_exists_seven_eighths_nonholes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:34:02.243029+00:00
-- url     : https://prove2.me/theorems/3bf1743b-b2fa-4b20-97c3-9d69b380a2bd
-- title:
--   DWZ Claim 6.8: one parameter leaves at least seven eighths nonholes
-- statement:
--   Let Ω be a nonempty finite parameter space and B a finite set of small blocks. For each block z, suppose that z is bad—equivalently, becomes a Step-2 hole—for at most one eighth of the parameters:
--
--   $$8\,|\{w\in\Omega:z\text{ is bad for }w\}|\le |\Omega|.$$
--
--   Then there is one parameter choice w for which at least seven eighths of all blocks are nonholes, in the exact division-free form
--
--   $$7|B|\le 8\,|\{z\in B:z\text{ is not bad for }w\}|.$$
--
--   This is the finite averaging step that turns the pointwise probability conclusion of DWZ Claim 6.8 into the nonhole fraction required by the Hole Lemma.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Claim 6.8 and the 'Bounding the value' paragraph immediately following it in Section 6.3.

import Theorems.Thm_mme_finset_incidence_double_count
import Theorems.Thm_mme_finite_collision_budget_averaging

open BigOperators Finset

set_option autoImplicit false

theorem mme_dwz_claim6_8_exists_seven_eighths_nonholes
    {Weight Block : Type}
    [Fintype Weight] [DecidableEq Weight] [Nonempty Weight]
    [Fintype Block] [DecidableEq Block]
    (bad : Block → Weight → Prop) [DecidableRel bad]
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (bad z)).card ≤ Fintype.card Weight) :
    ∃ w : Weight,
      7 * Fintype.card Block ≤
        8 * (Finset.univ.filter (fun z : Block ↦ ¬ bad z w)).card := by
  sorry

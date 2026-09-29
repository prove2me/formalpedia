-- Prove2me | Theorems.Thm_mme_stothers_phi233_uniform_cyclic_mode_degrees
-- name    : mme_stothers_phi233_uniform_cyclic_mode_degrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:07:12.530633+00:00
-- url     : https://prove2.me/theorems/541b9be0-5b42-41c9-b4e9-82bfa378c3c8
-- title:
--   Uniform cyclic mode degrees and target factorization for phi_233
-- statement:
--   For a valid nonempty phi_233 profile, define $D$ as the product of the three same-marginal fixed-word star sizes, $D_*$ as the corresponding product of exact-profile star sizes, and $V$ as the product of the three prescribed-word multinomial counts. Then every cyclic mode-star based at any target edge has ambient size exactly $D$ and target size exactly $D_*$. Moreover the whole cyclic target has size $V D_*$. Thus the concrete cyclic target is regular in all three modes, and its regular degree is exactly the quantity controlled by the cubic completion estimate.
-- source:
--   The regular cyclic-product degree structure used in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Theorems.Thm_mme_stothers_phi233_marginal_star_factorization
import Theorems.Thm_mme_stothers_phi233_exact_star_factorization
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem mme_stothers_phi233_uniform_cyclic_mode_degrees
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta)
    [DecidableEq (MME.StothersFourth.Phi233.CyclicModeWord N)] :
    let D := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 l = a.1.1 l}
    let Dstar := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta // b.1.1 l = a.1.1 l}
    let V := ∏ l : Fin 3,
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta l s).factorial)
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.ambientFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = D) ∧
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = Dstar) ∧
    (MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card = V * Dstar := by
  sorry

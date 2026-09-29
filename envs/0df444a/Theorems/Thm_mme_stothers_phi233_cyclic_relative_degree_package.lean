-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_relative_degree_package
-- name    : mme_stothers_phi233_cyclic_relative_degree_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:13:44.812297+00:00
-- url     : https://prove2.me/theorems/e5b8d791-cb0b-4a84-a329-8f84a34021af
-- title:
--   Complete relative-degree package for cyclic phi_233 extraction
-- statement:
--   Let a valid nonempty phi_233 profile have same-marginal/exact-profile cardinality ratio at most $R$, where $R\geq0$. Define $D$, $D_*$, and $V$ from the three ambient stars, exact stars, and word multinomials. Then every ambient cyclic mode-star based at a target edge has size at most $D$, every target cyclic mode-star has size exactly $D_*$, the target cardinality is $V D_*$, and $D\leq R^3D_*$. These are exactly the degree and target-factorization hypotheses needed by the sharp relative-degree hashing-and-pruning theorem.
-- source:
--   The completion-to-collision-degree step in the type-2 analysis of A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5.

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_uniform_cyclic_mode_degrees
import Theorems.Thm_mme_stothers_phi233_cyclic_star_ratio

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_relative_degree_package
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta)
    [DecidableEq (MME.StothersFourth.Phi233.CyclicModeWord N)]
    (R : ℝ) (hR : 0 ≤ R)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
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
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card ≤ D) ∧
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = Dstar) ∧
    ((MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card : ℝ) = (V : ℝ) * (Dstar : ℝ) ∧
    (D : ℝ) ≤ R ^ 3 * (Dstar : ℝ) := by
  sorry

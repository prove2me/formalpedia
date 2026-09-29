-- Prove2me | Theorems.Thm_mme_stothers_phi134_finite_power_block_certificate
-- name    : mme_stothers_phi134_finite_power_block_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:45:59.28007+00:00
-- url     : https://prove2.me/theorems/0a113b3e-3cc0-4dba-923b-4e9a04d398ad
-- title:
--   Finite retained-block certificate for a feasible phi_134 profile
-- statement:
--   Fix positive profile parameters $a,c$ and $\sigma=b+c$ with $c\leq\sigma$ and $\sigma+a\leq1$. For every nonnegative $V$ strictly below the unoptimized Davie--Stothers $\phi_{134}$ profile rate, there exist a positive integral scale $N$, counts $\alpha+\beta+\gamma+\delta=N$, and a retained family $F$ of cyclic exact eight-pattern profiles. The three mode projections are injective, and the associated blocks form a direct-sum restriction into the $2N$-th power of the literal cyclic $\phi_{134}$ constituent. For a common nonnegative block base $B$, every block attains each strict lower tau-value and $$ V^{2N}<|F|B. $$ This is the finite certificate produced by integral rounding, type-2 progression-free hashing, collision pruning, induced block zeroing, and the eight fine-component estimates in Lemma 5.1(iii). It is the sole source-specific combinatorial frontier after the optimizer and asymptotic closure have been separated out.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 3.3 and Lemma 5.1(iii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi134_profile_data
import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_finite_power_block_certificate
    {K : Type u} [Field K] (tau sigma a c : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((MME.StothersFourth.L 6 tau / sigma) ^ sigma *
            (MME.StothersFourth.E 6 tau / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((MME.StothersFourth.H 6 tau / 2) / c) ^ c *
            (MME.StothersFourth.E 6 tau / (1 - a - c)) ^
              (1 - a - c))) :
    ∃ (N alpha beta gamma delta : ℕ),
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      ∃ (kept : Finset
          (MME.StothersFourth.Phi134.CyclicExactEdge
            N alpha beta gamma delta))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi134.cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by
  sorry

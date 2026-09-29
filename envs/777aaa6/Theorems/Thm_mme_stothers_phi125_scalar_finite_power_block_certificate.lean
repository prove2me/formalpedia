-- Prove2me | Theorems.Thm_mme_stothers_phi125_scalar_finite_power_block_certificate
-- name    : mme_stothers_phi125_scalar_finite_power_block_certificate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:55:58.955142+00:00
-- url     : https://prove2.me/theorems/607e4aa5-285e-4be5-b01b-b4e5f9ec4f47
-- title:
--   Scalar finite block certificate below 4942080 for the q6 Stothers 125 constituent
-- statement:
--   Let $K$ be a field and $T$ the cyclic symmetrization of the $(1,2,5)$ constituent of the fourth Coppersmith–Winograd tensor power at $q=6$. For every real exponent $\tau$ and every $0\le V<4\,942\,080$, there exist $N>0$, nonnegative integers $\alpha+\beta+\gamma=N$, and a finite collection of cyclic exact-profile edges whose three mode projections are injective. There are tensors indexed by these edges and a nonnegative common bound $B$ such that their direct sum restricts to $T^{\otimes 2N}$ and each indexed tensor has $\tau$-value at least every $W$ with $0\le W<B$. The retained collection satisfies the strict surplus
--   $$V^{2N}<|\mathrm{kept}|B.$$
--   Thus a finite block certificate exists below the fixed scalar bound at every real exponent, including exponents below two thirds.
-- source:
--   The phi125 exact-profile and induced-hashing construction with scalar component values, specialized to the feasible parameters a=1/39 and b=36/55.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter
universe u
set_option autoImplicit false

theorem mme_stothers_phi125_scalar_finite_power_block_certificate
    {K : Type u} [Field K] (tau V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < 4942080) :
    ∃ (N alpha beta gamma : ℕ),
      0 < N ∧ alpha + beta + gamma = N ∧
      ∃ (kept : Finset
          (MME.StothersFourth.Phi125.CyclicExactEdge
            N alpha beta gamma))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi125.cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by sorry

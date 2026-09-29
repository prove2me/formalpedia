-- Prove2me | Theorems.Thm_mme_stothers_phi125_finite_power_block_certificate_no_upper_bound
-- name    : mme_stothers_phi125_finite_power_block_certificate_no_upper_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:49:27.630627+00:00
-- url     : https://prove2.me/theorems/1121eeaf-3a8e-4331-b6e8-61ccdfe458d1
-- title:
--   Finite block certificate for the q6 Stothers 125 constituent at every exponent at least two thirds
-- statement:
--   Let $K$ be a field and $T$ the cyclic symmetrization of the $(1,2,5)$ constituent of the fourth Coppersmith–Winograd tensor power at $q=6$. Let $3\tau\ge2$, $a,b>0$, and $a+b\le1$. Write $E=E(6,\tau)$, $H=H(6,\tau)$, and $L=L(6,\tau)$. For every nonnegative $V$ strictly smaller than
--   $$\frac4H(L/a)^a(EH/(1-a))^{1-a}(L/b)^b(2H/(1-b))^{1-b},$$
--   there exist $N>0$, nonnegative integers $\alpha+\beta+\gamma=N$, and a finite collection of cyclic exact-profile edges whose three mode projections are injective. There are tensors indexed by these edges and a nonnegative common bound $B$ such that their direct sum restricts to $T^{\otimes 2N}$, every indexed tensor has $\tau$-value at least every $W$ with $0\le W<B$, and $V^{2N}<|\mathrm{kept}|B$. No upper bound on the exponent or pre-existing cofinal extraction is assumed.
-- source:
--   Generalization of the accepted phi125 block-certificate construction: the exponent upper bound and supplied cofinal extraction are unused; the component bounds require only 3*tau >= 2.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter
universe u
set_option autoImplicit false

theorem mme_stothers_phi125_finite_power_block_certificate_no_upper_bound
    {K : Type u} [Field K] (tau a b : ℝ)
    (htauLower : 2 ≤ 3 * tau)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        4 / MME.StothersFourth.H 6 tau *
          ((MME.StothersFourth.L 6 tau / a) ^ a *
            ((MME.StothersFourth.E 6 tau *
              MME.StothersFourth.H 6 tau) / (1 - a)) ^ (1 - a)) *
          ((MME.StothersFourth.L 6 tau / b) ^ b *
            ((2 * MME.StothersFourth.H 6 tau) / (1 - b)) ^
              (1 - b))) :
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

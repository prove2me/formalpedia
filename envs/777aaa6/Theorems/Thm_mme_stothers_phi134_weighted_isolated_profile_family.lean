-- Prove2me | Theorems.Thm_mme_stothers_phi134_weighted_isolated_profile_family
-- name    : mme_stothers_phi134_weighted_isolated_profile_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:45:26.376631+00:00
-- url     : https://prove2.me/theorems/76c66ea5-4af5-47de-b34d-440be777fbf6
-- title:
--   Weighted isolated exact-profile family for Phi134
-- statement:
--   Assume $a,c>0$, $c\leq\sigma$, and $\sigma+a\leq1$. For positive component-value bases $L,E,H$, let $V\geq0$ lie strictly below the Davie--Stothers $\phi_{134}$ rate
--
--   $$8\left(\frac L\sigma\right)^\sigma\left(\frac E{1-\sigma}\right)^{1-\sigma}\left(\frac1a\right)^a\left(\frac{H/2}{c}\right)^c\left(\frac E{1-a-c}\right)^{1-a-c}.$$
--
--   Then there is a positive integral symmetric profile $\alpha+\beta+\gamma+\delta=N$ and a finite family $\mathcal F$ of cyclic exact-profile edges such that every one of its three vertex projections is injective, every coordinatewise-supported triple in $\mathcal F$ is diagonal, and
--
--   $$V^{2N}<|\mathcal F|L^{2\beta+2\gamma}E^{2\alpha+2\beta+4\delta}H^{2\gamma}.$$
--
--   This packages the finite profile surplus, the prime--Behrend labels, and sharp Type-2 hashing into the exact combinatorial family needed for the induced-block restriction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 3.3 and Lemma 5.1(iii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME Real BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_weighted_isolated_profile_family
    (sigma a c L E H V : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      ∃ kept : Finset (MME.StothersFourth.Phi134.CyclicExactEdge
          N alpha beta gamma delta),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi134.cyclicModeWord e.1 i)) ∧
        (∀ x y z : kept,
          MME.StothersFourth.Phi134.CyclicCoordinatewiseSupported
              x.1 y.1 z.1 →
            x = y ∧ y = z) ∧
        V ^ (2 * N) <
          (kept.card : ℝ) *
            (L ^ (2 * beta + 2 * gamma) *
              E ^ (2 * alpha + 2 * beta + 4 * delta) *
              H ^ (2 * gamma)) := by
  sorry

-- Prove2me | Theorems.Thm_mme_stothers_phi134_profile_cofinal_finite_extraction
-- name    : mme_stothers_phi134_profile_cofinal_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:33:50.208155+00:00
-- url     : https://prove2.me/theorems/68b4e124-197f-429e-8fa8-c95d21ec0b64
-- title:
--   Profile-parametric finite extraction for the Davie–Stothers phi_134 constituent
-- statement:
--   Let $2\leq 3\tau\leq3$. Choose positive profile parameters $a,c$ and put $\sigma=b+c$, subject to $c\leq\sigma$ and $\sigma+a\leq1$. For every nonnegative $V$ strictly below $$ 8\left(\frac L\sigma\right)^\sigma \left(\frac E{1-\sigma}\right)^{1-\sigma} \left(\frac1a\right)^a \left(\frac{H/2}{c}\right)^c \left(\frac E{1-a-c}\right)^{1-a-c}, $$ there are cofinal powers of the cyclic symmetrization of the literal $\phi_{134}$ constituent whose restrictions are direct sums of matrix-multiplication tensors with total $\tau$-weight at least $V$ to the power, up to a multiplicative loss tending to one. Here $E,H,L$ are the $q=6$ constituent values used by Davie and Stothers. This is the source-specific type-2 extraction before optimizing the profile; it isolates precisely the combinatorial and tensor-realization content of Lemma 5.1(iii).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_profile_cofinal_finite_extraction
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
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (x i) (y i) (z i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  sorry

-- Prove2me | Theorems.Thm_mme_stothers_phi125_profile_cofinal_finite_extraction
-- name    : mme_stothers_phi125_profile_cofinal_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:01:25.738297+00:00
-- url     : https://prove2.me/theorems/97c1eb89-fb40-4339-944b-480ce5dc0915
-- title:
--   Finite type-2 extraction for a feasible phi_125 profile
-- statement:
--   Fix positive real profile frequencies a,b with a+b≤1, corresponding to the normalized φ₁₂₅ parameters α/N and β/N (and γ/N=1−a−b). For every nonnegative base V strictly below $$ \frac{4}{H}\left(\frac{L}{a}\right)^a\left(\frac{EH}{1-a}\right)^{1-a}\left(\frac{L}{b}\right)^b\left(\frac{2H}{1-b}\right)^{1-b}, $$ there are cofinal powers of the cyclic symmetrization of the literal φ₁₂₅ constituent restricting to finite direct sums of matrix-multiplication tensors whose τ-weight is at least V to that power times a loss tending to one. This is the finite hashing and tensor-realization core of Davie–Stothers Lemma 5.1(ii), separated from the already proved optimizer substitution.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, type-2 hashing in Lemma 3.3 and the φ₁₂₅ extraction in Lemma 5.1(ii), printed pp. 359–361 and 364–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Theorems.Thm_mme_stothers_phi125_exact_iff_marginal_profile
import Theorems.Thm_mme_stothers_phi125_exact_profile_card
import Theorems.Thm_mme_stothers_phi125_fixed_mode_exact_profile_fiber_card

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_profile_cofinal_finite_extraction
    {K : Type u} [Field K] (tau a b : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
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
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (x i) (y i) (z i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  sorry

-- Prove2me | solution 1 for mme_complete_split_112_finite_common_numerator_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T13:07:03.486279+00:00
-- url     : https://prove2.me/submissions/6bd767c3-83bc-44d0-a0a5-d4cd1128926b

import Theorems.Thm_mme_complete_split_112_parametric_canonical_directional_rates

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

set_option autoImplicit false

theorem solution (q : ℕ) (hq : 0 < q) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 882 * n < 100 * q)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      ∀ n ∈ S,
        ∃ beta : Fin 3 → Profile 2,
          (∀ mode sigma, (beta mode).probability sigma =
            (profileProbability (((2 * n : ℕ) : ℚ) / (2 * (q : ℚ)))
              mode sigma : ℝ)) ∧
          ∃ A H : ℕ,
            ∃ family : CWQ6PrimaryHashFamily
              (q * m) ((2 * n) * m) ((q - 2 * n) * m) A H,
              0 < A ∧ H ≤ 4 ^ (q * m) ∧
              ((2 * (q * m) : ℕ) : ℝ) *
                (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤
                  Real.log (A : ℝ) ∧
              ((2 * (q * m) : ℕ) : ℝ) * (Real.log 2 - delta) ≤
                Real.log ((A : ℝ) * (H : ℝ)) := by
  classical
  let Good : ℕ → ℕ → Prop := fun n m =>
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (profileProbability (((2 * n : ℕ) : ℚ) / (2 * (q : ℚ)))
          mode sigma : ℝ)) ∧
      ∃ A H : ℕ,
        ∃ family : CWQ6PrimaryHashFamily
          (q * m) ((2 * n) * m) ((q - 2 * n) * m) A H,
          0 < A ∧ H ≤ 4 ^ (q * m) ∧
          ((2 * (q * m) : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤
              Real.log (A : ℝ) ∧
          ((2 * (q * m) : ℕ) : ℝ) * (Real.log 2 - delta) ≤
            Real.log ((A : ℝ) * (H : ℝ))
  have hEach : ∀ n : ℕ, 882 * n < 100 * q →
      ∀ᶠ m : ℕ in atTop, Good n m := by
    intro n hbound
    let l : ℕ := 2 * n
    let g : ℕ := q - 2 * n
    have hsum : l + g = q := by
      dsimp [l, g]
      omega
    have hbalance : 341 * l < 100 * g := by
      dsimp [l, g]
      omega
    rcases mme_complete_split_112_parametric_canonical_directional_rates.{0}
        l g hbalance with ⟨beta, hbeta, hrest⟩
    filter_upwards [hrest delta hdelta] with m hm
    rcases hm with ⟨A, H, family, hA, hH, hlogA, hlogAH, _⟩
    have hbeta' : ∀ mode sigma,
        (beta mode).probability sigma =
          (profileProbability (((2 * n : ℕ) : ℚ) / (2 * (q : ℚ)))
            mode sigma : ℝ) := by
      simpa [l, g, hsum] using hbeta
    have hfamily : CWQ6PrimaryHashFamily
        (q * m) ((2 * n) * m) ((q - 2 * n) * m) A H := by
      simpa [l, g, hsum] using family
    refine ⟨beta, hbeta', A, H, hfamily, hA, ?_, ?_, ?_⟩
    · simpa [l, g, hsum] using hH
    · simpa [l, g, hsum] using hlogA
    · simpa [l, g, hsum] using hlogAH
  have hAll : ∀ᶠ m : ℕ in atTop, ∀ n ∈ S, Good n m := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert n S hn ih =>
        have hbound := hS n (Finset.mem_insert_self n S)
        have hSbound : ∀ k ∈ S, 882 * k < 100 * q := by
          intro k hk
          exact hS k (Finset.mem_insert.mpr (Or.inr hk))
        have ih' := ih hSbound
        filter_upwards [hEach n hbound, ih'] with m hnResult hSResult
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hnResult
        · exact hSResult k hk
  simpa [Good] using hAll

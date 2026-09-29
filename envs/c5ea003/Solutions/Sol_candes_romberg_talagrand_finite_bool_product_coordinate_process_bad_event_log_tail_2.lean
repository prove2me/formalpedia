-- Prove2me | solution 2 for candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-30T03:32:51.819488+00:00
-- url     : https://prove2.me/submissions/bbe3f2fb-409d-43a7-80be-136428f96875

import Definitions.Def_matrix_completion_bernoulli_measure
import Theorems.Thm_candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n1 n2 : ℕ) (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n1 → Fin n2 → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n1, ∀ j : Fin n2, |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n1, ∑ j : Fin n2,
            (p : ℝ) * (1 - (p : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → ((Fin n1 × Fin n2) → Bool) → ℝ :=
          fun a ω =>
            ∑ i : Fin n1, ∑ j : Fin n2,
              ((cond (ω (i, j)) (1 : ℝ) 0 - (p : ℝ)) * coeff a i j)
        let boolZ : ((Fin n1 × Fin n2) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : ((Fin n1 × Fin n2) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (bernMeasure (n1 := n1) (n2 := n2) p hp).real
            {ω | ¬ |boolZ ω -
                  (∫ ω, boolZ ω ∂(bernMeasure (n1 := n1) (n2 := n2) p hp))| ≤ t} ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B *
                    (∫ ω, boolZbar ω
                      ∂(bernMeasure (n1 := n1) (n2 := n2) p hp))))) := by
  rcases candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail with
    ⟨K, hKpos, hK⟩
  refine ⟨K, hKpos, ?_⟩
  intro n1 n2 p hp ι hι hιne coeff B sigmaSq t hB hsigma ht hcoeff hvar
  let pairCoeff : ι → (Fin n1 × Fin n2) → ℝ :=
    fun a x => coeff a x.1 x.2
  have hcoeff_pair : ∀ a : ι, ∀ x : Fin n1 × Fin n2, |pairCoeff a x| ≤ B := by
    intro a x
    exact hcoeff a x.1 x.2
  have hvar_pair :
      ∀ a : ι,
        ∑ x : Fin n1 × Fin n2,
          (p : ℝ) * (1 - (p : ℝ)) * (pairCoeff a x) ^ 2 ≤ sigmaSq := by
    intro a
    simpa [pairCoeff, Fintype.sum_prod_type] using hvar a
  simpa [pairCoeff, bernMeasure, Fintype.sum_prod_type] using
    hK (Fin n1 × Fin n2) p hp ι pairCoeff B sigmaSq t hB hsigma ht
      hcoeff_pair hvar_pair

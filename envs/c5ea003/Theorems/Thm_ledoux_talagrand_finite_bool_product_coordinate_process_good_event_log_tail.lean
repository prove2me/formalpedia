-- Prove2me | Theorems.Thm_ledoux_talagrand_finite_bool_product_coordinate_process_good_event_log_tail
-- name    : ledoux_talagrand_finite_bool_product_coordinate_process_good_event_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T03:21:13.345502+00:00
-- url     : https://prove2.me/theorems/1bedaf90-df7a-42b8-9bb2-022175e4c3d6
-- statement:
--   Boolean product-measure Ledoux--Talagrand concentration for finite Bernoulli coordinate processes, in good-event form. Let $\omega:[n_1]\times[n_2]\to\{0,1\}$ be sampled from the product Bernoulli measure $\mathrm{bernMeasure}(p)$ with $p\le 1$. For a finite nonempty coefficient class $c_a(i,j)$, define $S_a(\omega)=\sum_{i,j}(\omega_{ij}-p)c_a(i,j)$, $Z(\omega)=\max_a S_a(\omega)$, and $\bar Z(\omega)=\max_a |S_a(\omega)|$. If $|c_a(i,j)|\le B$ and $\sum_{i,j}p(1-p)c_a(i,j)^2\le\sigma^2$, then a universal $K>0$ gives the logarithmic lower bound on the good event $|Z-\mathbb E Z|\le t$ with denominator $\sigma^2+B\mathbb E\bar Z$.
--
--   Source: Ledoux, *The Concentration of Measure Phenomenon*, Section 7, Corollary 7.8; Candès--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Section 3, Theorem 3.2/equation (3.9); cited by Candès--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2). This is a genuine analytic concentration leaf; the parent Candès--Romberg bad-event theorem is a formal complement bridge from this good-event form.
-- source:
--   Ledoux, The Concentration of Measure Phenomenon, Section 7, Corollary 7.8; Candes--Romberg, Sparsity and incoherence in compressive sampling, PDF p. 11, Section 3, Theorem 3.2/equation (3.9); cited by Candes--Recht, Exact Matrix Completion via Convex Optimization, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2).

import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

/-!
Ledoux--Talagrand finite Boolean product-measure concentration, in good-event
form.  This is the analytic child used to derive the Candès--Romberg bad-event
form by complementing the event.

Source: Ledoux, *The Concentration of Measure Phenomenon*, Section 7,
Corollary 7.8; Candès--Romberg, *Sparsity and incoherence in compressive
sampling*, PDF p. 11, Section 3, Theorem 3.2/equation (3.9); cited by
Candès--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1,
PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2).
-/

theorem ledoux_talagrand_finite_bool_product_coordinate_process_good_event_log_tail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ : ℕ) (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (p : ℝ) * (1 - (p : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun a ω =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              ((cond (ω (i, j)) (1 : ℝ) 0 - (p : ℝ)) * coeff a i j)
        let boolZ : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (bernMeasure (n1 := n₁) (n2 := n₂) p hp).real
            {ω | |boolZ ω -
                  (∫ ω, boolZ ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))| ≤ t} ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B *
                      (∫ ω, boolZbar ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))))) := by
  sorry

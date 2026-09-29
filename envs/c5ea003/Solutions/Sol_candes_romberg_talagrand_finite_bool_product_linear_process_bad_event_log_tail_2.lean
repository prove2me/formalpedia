-- Prove2me | solution 2 for candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T06:09:39.563544+00:00
-- url     : https://prove2.me/submissions/e251a26a-290c-4e25-82ae-baa91b81b7ec

import Theorems.Thm_TalagrandCore_candes_romberg_talagrand_leaf

open MeasureTheory
open scoped Classical BigOperators

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (κ : Type) [Fintype κ] (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → κ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ x : κ, |coeff a x| ≤ B) →
        (∀ a : ι,
          ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * (coeff a x) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → (κ → Bool) → ℝ :=
          fun a ω =>
            ∑ x : κ, ((cond (ω x) (1 : ℝ) 0 - (p : ℝ)) * coeff a x)
        let boolZ : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)).real
            {ω | ¬ |boolZ ω -
                  (∫ ω, boolZ ω
                    ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))| ≤ t} ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B *
                    (∫ ω, boolZbar ω
                      ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))))) := by
  exact TalagrandCore.candes_romberg_talagrand_leaf

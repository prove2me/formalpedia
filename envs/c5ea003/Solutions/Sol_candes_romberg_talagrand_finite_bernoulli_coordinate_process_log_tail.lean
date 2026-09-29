-- Prove2me | solution 1 for candes_romberg_talagrand_finite_bernoulli_coordinate_process_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-29T22:52:59.233777+00:00
-- url     : https://prove2.me/submissions/96f46ea1-10b0-4b4e-87b2-201c3be391a0

import Theorems.Thm_candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

private theorem bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega) = 1 := by
  classical
  unfold bernoulliObservationWeight
  simpa using
    (Fintype.sum_pow_mul_eq_add_pow (Fin n₁ × Fin n₂) p (1 - p) :
      (∑ s : Finset (Fin n₁ × Fin n₂),
        p ^ s.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - s.card)) =
          (p + (1 - p)) ^ Fintype.card (Fin n₁ × Fin n₂))

private theorem bernoulliEventProb_compl_ge_one_sub
    {n₁ n₂ : ℕ} {p eps : ℝ}
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p (fun Omega => ¬ Event Omega) ≤ eps →
    bernoulliEventProb p Event ≥ 1 - eps := by
  classical
  intro hbad
  have hbad_sum :
      (∑ Omega : Finset (Fin n₁ × Fin n₂),
        if Event Omega then 0 else bernoulliObservationWeight p Omega) ≤ eps := by
    rw [show
      (∑ Omega : Finset (Fin n₁ × Fin n₂),
        if Event Omega then 0 else bernoulliObservationWeight p Omega) =
          bernoulliEventProb p (fun Omega => ¬ Event Omega) by
        unfold bernoulliEventProb
        refine Finset.sum_congr rfl ?_
        intro Omega _hOmega
        by_cases h : Event Omega <;> simp [h]]
    exact hbad
  have hpartition :
      (∑ Omega : Finset (Fin n₁ × Fin n₂),
          if Event Omega then bernoulliObservationWeight p Omega else 0) +
        (∑ Omega : Finset (Fin n₁ × Fin n₂),
          if Event Omega then 0 else bernoulliObservationWeight p Omega) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ Omega : Finset (Fin n₁ × Fin n₂),
          ((if Event Omega then bernoulliObservationWeight p Omega else 0) +
            if Event Omega then 0 else bernoulliObservationWeight p Omega)) =
          ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega := by
            refine Finset.sum_congr rfl ?_
            intro Omega _hOmega
            by_cases h : Event Omega <;> simp [h]
      _ = 1 := bernoulliObservationWeight_sum_eq_one (n₁ := n₁) (n₂ := n₂) (p := p)
  unfold bernoulliEventProb
  linarith

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let process : ι → Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun a Omega =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeff a i j)
        let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Omega)
        let Zbar : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun a : ι => |process a Omega|)
        bernoulliEventProb p
            (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B * bernoulliExpectation p Zbar))) := by
  rcases candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail with
    ⟨K, hK, hbad_all⟩
  refine ⟨K, hK, ?_⟩
  intro n₁ n₂ m ι _instFintype _instNonempty coeff B sigmaSq t
    hn₁ hn₂ hmle hB hsigma ht hcoeff hvariance
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let process : ι → Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun a Omega =>
      ∑ i : Fin n₁, ∑ j : Fin n₂,
        (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff a i j)
  let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Omega)
  let Zbar : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |process a Omega|)
  have hbad :
      bernoulliEventProb p
          (fun Omega => ¬ |Z Omega - bernoulliExpectation p Z| ≤ t) ≤
        3 * Real.exp
          (-(t / (K * B)) *
            Real.log
              (1 + (B * t) /
                (sigmaSq + B * bernoulliExpectation p Zbar))) := by
    simpa [p, process, Z, Zbar] using
      hbad_all n₁ n₂ m ι coeff B sigmaSq t
        hn₁ hn₂ hmle hB hsigma ht hcoeff hvariance
  exact
    bernoulliEventProb_compl_ge_one_sub
      (n₁ := n₁) (n₂ := n₂) (p := p)
      (eps := 3 * Real.exp
        (-(t / (K * B)) *
          Real.log
            (1 + (B * t) /
              (sigmaSq + B * bernoulliExpectation p Zbar))))
      (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) hbad

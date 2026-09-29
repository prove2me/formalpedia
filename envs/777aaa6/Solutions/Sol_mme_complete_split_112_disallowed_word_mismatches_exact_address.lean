-- Prove2me | solution 1 for mme_complete_split_112_disallowed_word_mismatches_exact_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:20:58.586452+00:00
-- url     : https://prove2.me/submissions/c3283f81-32ad-4843-be4d-56c193a0d60e

import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Theorems.Thm_mme_complete_split_112_exact_address_histogram
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open MME MME.CompleteSplit MME.CompleteSplit112 MME.DWZComponentRestriction
open scoped NNReal

universe u v

private theorem mismatch_of_histogram
    {ι : Type u} {κ : Type v} {ell N : ℕ}
    (label : κ → CompleteWord ell) (grade : ι → κ)
    (beta : Profile ell) (epsilon : ℝ≥0) (w : PowIndex ι N)
    (address : Fin N → κ)
    (hhist : ∀ sigma : CompleteWord ell,
      (Fintype.card {r : Fin N // label (address r) = sigma} : ℝ) =
        (N : ℝ) * beta.probability sigma)
    (hnot : ¬ ApproxConsistent (label ∘ grade) beta epsilon w) :
    ∃ r : Fin N, grade (PowIndex.get N w r) ≠ address r := by
  by_contra hbad
  push_neg at hbad
  apply hnot
  intro sigma
  have hcount : wordCount (label ∘ grade) w sigma =
      Fintype.card {r : Fin N // label (address r) = sigma} := by
    rw [Fintype.card_subtype]
    unfold wordCount
    congr 1
    ext r
    simp [hbad r]
  rw [hcount, hhist, sub_self, abs_zero]
  positivity

theorem solution :
    (∀ {ι : Type u} (N L G : ℕ) (p : ℚ),
      L + G = N → (L : ℚ) = (2 * N : ℕ) * p →
      ∀ (mode : Fin 3) (grade : ι → Fin 3) (beta : Profile 2),
        (∀ sigma, beta.probability sigma = (profileProbability p mode sigma : ℝ)) →
        ∀ (epsilon : ℝ≥0) (w : PowIndex ι (2 * N)),
          ¬ ApproxConsistent (fineWord mode ∘ grade) beta epsilon w →
          ∀ address : CWQ6ExactCoupledAddress N L G,
            ∃ r : Fin (2 * N),
              grade (PowIndex.get (2 * N) w r) ≠ address.1 mode r) ∧
    (∀ (q m : ℕ) (mode : Fin 3) (beta : Profile 2),
      (∀ sigma, beta.probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) →
      ∀ (epsilon : ℝ≥0)
        (w : PowIndex (LiftedCoord.{u} q mode)
          (2 * (1180591620717411303424 * m))),
        ¬ ApproxConsistent (fineWord mode ∘ liftedCoordGrade q mode) beta epsilon w →
        ∀ address : CWQ6ExactCoupledAddress
          (1180591620717411303424 * m)
          (8959763742786037 * m)
          (1180582660953668517387 * m),
          ∃ r : Fin (2 * (1180591620717411303424 * m)),
            liftedCoordGrade q mode
                (PowIndex.get (2 * (1180591620717411303424 * m)) w r) ≠
              address.1 mode r) := by
  constructor
  · intro ι N L G p hLG hLp mode grade beta hbeta epsilon w hnot address
    apply mismatch_of_histogram (ell := 2) (N := 2 * N)
      (fineWord mode) grade beta epsilon w
      (address.1 mode) ?_ hnot
    intro sigma
    rw [hbeta sigma]
    exact_mod_cast (mme_complete_split_112_exact_address_histogram.1
      N L G p hLG hLp address mode sigma)
  · intro q m mode beta hbeta epsilon w hnot address
    apply mismatch_of_histogram (ell := 2) (N := 2 * (1180591620717411303424 * m))
      (fineWord mode) (liftedCoordGrade q mode) beta epsilon w
      (address.1 mode) ?_ hnot
    intro sigma
    rw [hbeta sigma]
    exact mme_complete_split_112_exact_address_histogram.2 m address mode sigma

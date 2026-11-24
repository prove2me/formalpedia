-- Prove2me | solution 1 for Cryptography.GradedEncoding.DecisionGame.advantage_le_of_world_gaps
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:45:59.423975+00:00
-- url     : https://prove2.me/submissions/8cc0ed38-f0d2-4bb1-a7ab-e040e698cb04

-- Thm stub generated from Cryptography/GradedEncoding/SecurityReduction.lean
import Mathlib
import Definitions.Def_Cryptography_GradedEncoding_Foundations
import Definitions.Def_Cryptography_GradedEncoding_SecurityReduction
import Definitions.Def_Cryptography_LWE_OperationalSecurity

/-!
# Security reductions for multilinear graded encodings

The reduction layer is independent of any particular graded-encoding candidate.
A decisional multilinear Diffie--Hellman game is represented by its two finite
transcript distributions. A perfect reduction is an equivalence of transcript
spaces preserving both distributions pointwise. The main theorem proves exact
preservation of every deterministic distinguisher's advantage and transfers any
source hardness bound to the graded target game.
-/

-- open removed: section is not a namespace

noncomputable section

open Cryptography.GradedEncoding


open DecisionGame

variable {Ω : Type*} [Fintype Ω]





variable {Source Target : Type*} [Fintype Source] [Fintype Target]


open PerfectReduction

variable {source : DecisionGame Source} {target : DecisionGame Target}







open DecisionGame

open Finset BigOperators
noncomputable section
open LWEOperational

namespace LWEOperational

theorem expectation_sub_le_l1Gap_aux {Ω : Type*} [Fintype Ω]
    (P Q : FinitePMF Ω) (test : Ω → ℝ)
    (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
    |expectation P test - expectation Q test| ≤ l1Gap P Q := by
  rw [expectation, expectation, l1Gap, ← Finset.sum_sub_distrib]
  calc
    |∑ x, (P.mass x * test x - Q.mass x * test x)|
        ≤ ∑ x, |P.mass x * test x - Q.mass x * test x| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |P.mass x - Q.mass x| * |test x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← abs_mul]
          congr 1
          ring
    _ ≤ ∑ x, |P.mass x - Q.mass x| := by
          apply Finset.sum_le_sum
          intro x _
          rw [abs_of_nonneg (htest x).1]
          exact mul_le_of_le_one_right (abs_nonneg _) (htest x).2

theorem boolean_distinguisher_advantage_aux {Ω : Type*} [Fintype Ω]
    (P Q : FinitePMF Ω) (adversary : Ω → Bool) :
    |(∑ x with adversary x = true, P.mass x) -
      (∑ x with adversary x = true, Q.mass x)| ≤ l1Gap P Q := by
  let test : Ω → ℝ := fun x => if adversary x = true then 1 else 0
  have htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1 := by
    intro x
    simp only [test]
    split_ifs <;> norm_num
  have h := expectation_sub_le_l1Gap_aux P Q test htest
  simpa [expectation, test, Finset.sum_filter] using h

end LWEOperational

theorem solution {Ω : Type*} [Fintype Ω]
    (source target : DecisionGame Ω) (A : Ω → Bool) (δfalse δtrue : ℝ)
    (hfalse : LWEOperational.l1Gap
      (target.experiment.challenge false)
      (source.experiment.challenge false) ≤ δfalse)
    (htrue : LWEOperational.l1Gap
      (target.experiment.challenge true)
      (source.experiment.challenge true) ≤ δtrue) :
    target.advantage A ≤ source.advantage A + δfalse + δtrue := by
  have hf := LWEOperational.boolean_distinguisher_advantage_aux
    (target.experiment.challenge false)
    (source.experiment.challenge false) A
  have ht := LWEOperational.boolean_distinguisher_advantage_aux
    (target.experiment.challenge true)
    (source.experiment.challenge true) A
  have htriangle :
      |target.acceptance true A - target.acceptance false A| ≤
        |source.acceptance true A - source.acceptance false A| +
        |target.acceptance false A - source.acceptance false A| +
        |target.acceptance true A - source.acceptance true A| := by
    calc
      |target.acceptance true A - target.acceptance false A| =
          |(source.acceptance true A - source.acceptance false A) +
            (target.acceptance true A - source.acceptance true A) +
            (source.acceptance false A - target.acceptance false A)| := by
              congr 1
              ring
      _ ≤ |source.acceptance true A - source.acceptance false A| +
            |target.acceptance true A - source.acceptance true A| +
            |source.acceptance false A - target.acceptance false A| :=
              abs_add_three _ _ _
      _ = |source.acceptance true A - source.acceptance false A| +
            |target.acceptance false A - source.acceptance false A| +
            |target.acceptance true A - source.acceptance true A| := by
              rw [abs_sub_comm (source.acceptance false A)]
              ring
  simp only [advantage, acceptance] at htriangle ⊢
  exact htriangle.trans (by linarith [hf.trans hfalse, ht.trans htrue])

#print axioms solution

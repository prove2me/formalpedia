-- Prove2me | solution 1 for mme_released_interior_112_intact_family_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:29:38.452931+00:00
-- url     : https://prove2.me/submissions/a9ff0edd-1ec1-492c-a0cf-63226e90cc64

import Theorems.Thm_mme_released_interior_child_parameter_bound
import Theorems.Thm_mme_released_interior_112_canonical_probability
import Theorems.Thm_mme_complete_split_112_coupled_restricted_family_certificate
import Theorems.Thm_mme_complete_split_112_canonical_profile_router
import Theorems.Thm_mme_complete_split_112_canonical_power_restricts_from_intact
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.CompleteSplit112
universe u

private theorem canonical_probability_sum (p : ℚ) (i : Fin 3) :
    ∑ w : CompleteWord 2, profileProbability p i w = 1 := by
  change (∑ w : Fin 2 → Fin 3, profileProbability p i w) = 1
  rw [Fintype.sum_equiv (finTwoArrowEquiv (Fin 3))
    (fun w => profileProbability p i w)
    (fun ab => profileProbability p i ![ab.1, ab.2]) (by
      intro w
      congr 1
      funext j
      fin_cases j <;> rfl)]
  fin_cases i <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, profileProbability]
  all_goals ring

/-- Every canonical ordering of a released 112 child admits an intact
family certificate with the exact integer marginal counts and matrix volume.
The construction includes zero outer parameters. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1)
    (m A H : ℕ) (K : Type u) [Field K] :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
    CWQ6PrimaryHashFamily (denominator * m) ((2 * p) * m)
      ((denominator - 2 * p) * m) A H →
    Nonempty (CTensorOneHOneFamilyCertificate
      (CWCells.unbroken K 5 2 (2 * (denominator * m)) (Equiv.refl _)
        (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
        (fun i _ w => 2 * m * childMarginal owner s r c (Equiv.swap z 2 i) w))
      A H (5 ^ (4 * ((denominator - 2 * p) * m) + 2 * ((2 * p) * m)))) := by
  dsimp only
  intro family
  let p := (((seed owner s).children.find?
    (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
  have hp : p ≤ denominator / 2 :=
    mme_released_interior_child_parameter_bound owner s r (sourceShape owner c)
  have hprob := mme_released_interior_112_canonical_probability owner s r c z hshape
  let beta (i : Fin 3) : Profile 2 := {
    level_pos := by decide
    probability w := (childMarginal owner s r c (Equiv.swap z 2 i) w : ℝ) / denominator
    nonnegative w := by positivity
    sum_eq_one := by
      have hq : (∑ w : CompleteWord 2,
          (childMarginal owner s r c (Equiv.swap z 2 i) w : ℚ) / denominator) = 1 := by
        simp only [hprob]
        exact canonical_probability_sum _ i
      have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
      push_cast at hr
      exact hr }
  have hbeta (i : Fin 3) (w : CompleteWord 2) :
      (beta i).probability w = (profileProbability ((p : ℚ) / denominator) i w : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hprob i w)
    simpa only [beta, Rat.cast_div, Rat.cast_natCast] using h
  have hLG : (2 * p) * m + (denominator - 2 * p) * m = denominator * m := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (by norm_num [denominator] at hp ⊢; omega)]
  have hLp : (((2 * p) * m : ℕ) : ℚ) =
      ((2 * (denominator * m) : ℕ) : ℚ) * ((p : ℚ) / denominator) := by
    push_cast
    norm_num [denominator]
    ring
  obtain ⟨certificate⟩ := mme_complete_split_112_coupled_restricted_family_certificate
    (K := K) 5 ((p : ℚ) / denominator) hLG hLp family beta hbeta 0
  have hmu (i : Fin 3) (w : CompleteWord 2) :
      ((2 * m * childMarginal owner s r c (Equiv.swap z 2 i) w : ℕ) : ℝ) =
        ((2 * (denominator * m) : ℕ) : ℝ) * (beta i).probability w := by
    dsimp [beta]
    push_cast
    norm_num [denominator]
    ring
  exact ⟨{
    star := certificate.star
    restrict := certificate.restrict.trans
      ((mme_complete_split_112_canonical_profile_router K 5 beta 0
        (2 * (denominator * m))).trans
        (mme_complete_split_112_canonical_power_restricts_from_intact K 5
          (2 * (denominator * m)) beta
          (fun i w => 2 * m * childMarginal owner s r c (Equiv.swap z 2 i) w) hmu))
    certificate := certificate.certificate
  }⟩


#print axioms solution

-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearAlternation.eq_zero_of_endpoint_zeros_and_alternation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:57:38.485294+00:00
-- url     : https://prove2.me/submissions/4a33a12f-0e70-4152-bd2c-9c7cd8cb47e3

import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_exists_root_between_of_eval_mul_neg
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

namespace ErdosProblems.Erdos1041.SharpCollinearAlternation
end ErdosProblems.Erdos1041.SharpCollinearAlternation

/-!
# Sharp constrained alternation for the collinear Erdős #1041 case

This module isolates the rigidity argument behind the sharp adjacent-gap
estimate.  If two monic real polynomials of the same degree agree at the two
endpoints, the second polynomial cannot be uniformly smaller than the first
at a full alternating sequence of interior peaks: otherwise their difference
has one zero between each consecutive pair of peaks as well as the two
endpoint zeros, although its degree has dropped by one.

The intended comparison polynomial is the endpoint-normalised scaled
Chebyshev polynomial.  Keeping the alternation engine independent of that
instantiation makes the root-counting step reusable and auditable.
-/

namespace ErdosProblems.Erdos1041.SharpCollinearAlternation
open Set
open Polynomial
end ErdosProblems.Erdos1041.SharpCollinearAlternation

open Set
open Polynomial
open ErdosProblems.Erdos1041.SharpCollinearAlternation in
theorem solution
    {n : ℕ} {p : ℝ[X]} {a b : ℝ} {c : Fin (n + 1) → ℝ}
    (hc : StrictMono c) (ha : a < c 0) (hb : c (Fin.last n) < b)
    (hpa : p.eval a = 0) (hpb : p.eval b = 0)
    (halt : ∀ i : Fin n,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hdeg : p.natDegree < n + 2) :
    p = 0 := by
  classical
  have hex (i : Fin n) :
      ∃ x ∈ Ioo (c i.castSucc) (c i.succ), p.eval x = 0 :=
    exists_root_between_of_eval_mul_neg (hc i.castSucc_lt_succ) (halt i)
  choose z hzmem hzroot using hex
  have hzinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hcij : c i.succ ≤ c j.castSucc :=
        hc.monotone (Fin.succ_le_castSucc_iff.mpr hijlt)
      have hzlt : z i < z j := lt_of_lt_of_le (hzmem i).2
        (le_trans hcij (hzmem j).1.le)
      exact (ne_of_lt hzlt) hij
    · have hcji : c j.succ ≤ c i.castSucc :=
        hc.monotone (Fin.succ_le_castSucc_iff.mpr hjilt)
      have hzlt : z j < z i := lt_of_lt_of_le (hzmem j).2
        (le_trans hcji (hzmem i).1.le)
      exact (ne_of_gt hzlt) hij
  let Z : Finset ℝ := Finset.univ.image z
  have hcardZ : Z.card = n := by
    simp [Z, Finset.card_image_of_injective _ hzinj]
  have haZ : a ∉ Z := by
    simp only [Z, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i
    have haci : a < c i.castSucc := lt_of_lt_of_le ha
      (hc.monotone (Fin.zero_le _))
    exact ne_of_gt (lt_trans haci (hzmem i).1)
  have hbZ : b ∉ Z := by
    simp only [Z, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i
    have hcib : c i.succ < b := lt_of_le_of_lt
      (hc.monotone (Fin.le_last _)) hb
    exact ne_of_lt (lt_trans (hzmem i).2 hcib)
  have hab : a ≠ b := by
    exact ne_of_lt (lt_trans ha (lt_of_le_of_lt (hc.monotone (Fin.zero_le _)) hb))
  let S : Finset ℝ := insert a (insert b Z)
  have hcardS : S.card = n + 2 := by
    simp [S, Finset.card_insert_of_notMem, haZ, hbZ, hab, hcardZ]
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S
  · intro x hx
    simp only [S, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hxZ
    · exact hpa
    · exact hpb
    · rcases Finset.mem_image.mp hxZ with ⟨i, _hi, rfl⟩
      exact hzroot i
  · simpa [hcardS] using hdeg

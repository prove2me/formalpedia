-- Prove2me | solution 1 for ErdosProblems.Erdos1041.SharpCollinearAlternation.exists_peak_le_of_monic_comparison
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T03:59:00.179529+00:00
-- url     : https://prove2.me/submissions/0af7c2af-cd9d-4c5c-9f23-2cafc044e411

import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_eq_zero_of_endpoint_zeros_and_alternation
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearAlternation_sub_mul_self_pos_of_abs_lt_abs
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



/-- Pointwise domination preserves an alternating sign change after
subtraction. -/
theorem sub_values_mul_neg_of_abs_lt_abs
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ * x₂ < 0)
    (h₁ : |y₁| < |x₁|) (h₂ : |y₂| < |x₂|) :
    (x₁ - y₁) * (x₂ - y₂) < 0 := by
  have hs₁ := sub_mul_self_pos_of_abs_lt_abs h₁
  have hs₂ := sub_mul_self_pos_of_abs_lt_abs h₂
  rcases mul_neg_iff.mp hx with hsign | hsign
  · have hsub₁ : 0 < x₁ - y₁ := by nlinarith [hs₁]
    have hsub₂ : x₂ - y₂ < 0 := by nlinarith [hs₂]
    exact mul_neg_of_pos_of_neg hsub₁ hsub₂
  · have hsub₁ : x₁ - y₁ < 0 := by nlinarith [hs₁]
    have hsub₂ : 0 < x₂ - y₂ := by nlinarith [hs₂]
    exact mul_neg_of_neg_of_pos hsub₁ hsub₂
end ErdosProblems.Erdos1041.SharpCollinearAlternation

open Set
open Polynomial
open ErdosProblems.Erdos1041.SharpCollinearAlternation in
theorem solution
    {n : ℕ} {p u : ℝ[X]} {a b C : ℝ} {c : Fin (n + 1) → ℝ}
    (hp : p.IsMonicOfDegree (n + 2)) (hu : u.IsMonicOfDegree (n + 2))
    (hc : StrictMono c) (ha : a < c 0) (hb : c (Fin.last n) < b)
    (hpa : p.eval a = 0) (hpb : p.eval b = 0)
    (hua : u.eval a = 0) (hub : u.eval b = 0)
    (hpalt : ∀ i : Fin n,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hubound : ∀ i : Fin (n + 1), |u.eval (c i)| ≤ C) :
    ∃ i : Fin (n + 1), |p.eval (c i)| ≤ C := by
  by_contra hnone
  have hnone' : ∀ i : Fin (n + 1), C < |p.eval (c i)| := by
    intro i
    exact lt_of_not_ge (fun hi ↦ hnone ⟨i, hi⟩)
  let h := p - u
  have hah : h.eval a = 0 := by simp [h, eval_sub, hpa, hua]
  have hbh : h.eval b = 0 := by simp [h, eval_sub, hpb, hub]
  have halt (i : Fin n) :
      h.eval (c i.castSucc) * h.eval (c i.succ) < 0 := by
    rw [show h.eval (c i.castSucc) =
        p.eval (c i.castSucc) - u.eval (c i.castSucc) by simp [h, eval_sub],
      show h.eval (c i.succ) =
        p.eval (c i.succ) - u.eval (c i.succ) by simp [h, eval_sub]]
    apply sub_values_mul_neg_of_abs_lt_abs (hpalt i)
    · exact lt_of_le_of_lt (hubound i.castSucc) (hnone' i.castSucc)
    · exact lt_of_le_of_lt (hubound i.succ) (hnone' i.succ)
  have hdeg : h.natDegree < n + 2 := by
    exact hp.natDegree_sub_lt (by simp) hu
  have hz : h = 0 :=
    eq_zero_of_endpoint_zeros_and_alternation hc ha hb hah hbh halt hdeg
  have hpu : p = u := sub_eq_zero.mp hz
  have hle := hubound (0 : Fin (n + 1))
  have hgt := hnone' (0 : Fin (n + 1))
  rw [hpu] at hgt
  exact (not_lt_of_ge hle) hgt

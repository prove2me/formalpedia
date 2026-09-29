-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T04:06:10.75393+00:00
-- url     : https://prove2.me/submissions/ac14bde6-76cf-4862-b464-a1d9a325e2fb

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_chebNode_strictMono
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_chebNode_zero
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_eval_monicScaledChebyshev
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_monicScaledChebyshev_eq_prod
import Mathlib
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Erdős 1041: the sharp Chebyshev bound for collinear roots, with sharpness

Paper-form restatement of

* `res:sharp-collinear-root-diameter`
  (`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 1155),
* `thm:sharp-collinear-diameter`
  (`paper/reasoning-parts/erdos1041/core.tex`, line 1715),
* `cor:collinear-erdos-1041`
  (`paper/reasoning-parts/erdos1041/core.tex`, line 1769).

A monic complex polynomial of degree `n` whose zero occurrences are collinear is
written here in its factored form `∏ k, (X - C (base + dir * y k))` with
`‖dir‖ = 1` and `y : Fin n → ℝ`: that is exactly "monic of degree `n` with all
zero occurrences on one line", the line being `base + dir * ℝ`.  The diameter
`D` of the zero occurrences is carried as the hypothesis that `D` is the
greatest pairwise distance between zero occurrences.

The existing tree modules `SharpCollinearAlternation` and
`SharpCollinearChebyshev` supply the alternation/Chebyshev kernel: for a monic
real `p` of degree `m + 2` vanishing at `±1` and alternating in sign at `m + 1`
ordered interior points, one of those points has `|p| ≤ comparisonBound (m+2)`.
This file supplies everything the paper's proof needs around that kernel:

* the rigid normalisation (translation, rotation, scaling by `R = D/2`) and the
  transport identity `‖f (base + dir * s)‖ = R ^ n * |q ((s - mid)/R)|`;
* the existence of a maximiser of `|q|` in each root gap, and the fact that it
  is interior;
* the sign alternation of those gap maxima, proved directly from the product
  form of `q`;
* the upgrade from the kernel's pointwise conclusion to a bound on the WHOLE
  selected segment, which is where "`c i` is the gap maximum" is used;
* the repeated-zero (constant path) case;
* the sharpness clauses: the scaled Chebyshev configuration, its extreme zeros
  at distance `D`, a point of every adjacent gap at which the bound is attained
  with equality, and hence that no smaller constant works in any degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21
open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev

/-! ### The constant `C_n = 1 / (2^(n-1) cos^n (π/(2n)))` -/









/-! ### A monic product of linear factors -/



/-! ### Sign alternation between consecutive root gaps -/



/-! ### Gap maxima -/



/-! ### The normalised core: a whole gap below `C_n` -/



/-! ### Transport between the root line and `ℝ` -/

theorem dist_collinear (base dir : ℂ) (hdir : ‖dir‖ = 1) (a b : ℝ) :
    dist (base + dir * (a : ℂ)) (base + dir * (b : ℂ)) = |a - b| := by
  rw [dist_eq_norm]
  have h : base + dir * (a : ℂ) - (base + dir * (b : ℂ)) = dir * ((a - b : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, norm_mul, hdir, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_eval_collinear {n : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1) (y : Fin n → ℝ)
    (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ)))) (s : ℝ) :
    ‖f.eval (base + dir * (s : ℂ))‖ = |∏ k, (s - y k)| := by
  subst hf
  rw [eval_prod]
  have hfac : ∀ k : Fin n,
      (X - C (base + dir * (y k : ℂ))).eval (base + dir * (s : ℂ))
        = dir * ((s - y k : ℝ) : ℂ) := by
    intro k; simp only [eval_sub, eval_X, eval_C]; push_cast; ring
  rw [Finset.prod_congr rfl fun k _ => hfac k, norm_prod]
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [norm_mul, hdir, one_mul, Complex.norm_real, Real.norm_eq_abs]





/-! ### The sharp collinear root-diameter theorem -/



/-! ### The Erdős case: a short curve inside the unit lemniscate -/



/-! ### Sharpness: the scaled Chebyshev root configuration -/

private theorem angle_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.pi / b :=
  div_nonneg (mul_nonneg ha Real.pi_pos.le) hb.le

private theorem angle_le_pi {a b : ℝ} (hb : 0 < b) (h : a ≤ b) :
    a * Real.pi / b ≤ Real.pi := by
  have h1 : a / b ≤ 1 := (div_le_one hb).mpr h
  have h2 : a * Real.pi / b = Real.pi * (a / b) := by ring
  rw [h2]
  nlinarith [Real.pi_pos]

private theorem angle_lt {a a' b : ℝ} (hb : 0 < b) (h : a < a') :
    a * Real.pi / b < a' * Real.pi / b :=
  div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hb

/-- `cos` of an angle `a π / b` is strictly decreasing in `a` on the admissible
range `0 ≤ a' < a ≤ b`. -/
private theorem cos_angle_lt {a a' b : ℝ} (hb : 0 < b) (ha' : 0 ≤ a') (hab : a ≤ b)
    (h : a' < a) :
    Real.cos (a * Real.pi / b) < Real.cos (a' * Real.pi / b) :=
  Real.cos_lt_cos_of_nonneg_of_le_pi (angle_nonneg ha' hb) (angle_le_pi hb hab)
    (angle_lt hb h)





private theorem endpointScale_pos' (m : ℕ) : 0 < endpointScale (m + 2) :=
  endpointScale_pos (Nat.le_add_left 2 m)

private theorem twoN_pos (m : ℕ) : (0 : ℝ) < 2 * ((m + 2 : ℕ) : ℝ) := by
  have h : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (m + 1)
  linarith





theorem chebNode_last (m : ℕ) : chebNode m (Fin.last (m + 1)) = 1 := by
  have hr := endpointScale_pos' m
  have hidx : (m + 1 - ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) : ℕ) = 0 := by simp
  have hang : (2 * ((0 : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ))
      = Real.pi / (2 * ((m + 2 : ℕ) : ℝ)) := by norm_num
  have hes : endpointScale (m + 2) = Real.cos (Real.pi / (2 * ((m + 2 : ℕ) : ℝ))) := rfl
  simp only [chebNode, hidx]
  rw [hang, ← hes]
  field_simp

theorem chebNode_abs_le (m : ℕ) (i : Fin (m + 2)) : |chebNode m i| ≤ 1 := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [← chebNode_zero m]; exact (chebNode_strictMono m).monotone (Fin.zero_le i)
  · rw [← chebNode_last m]; exact (chebNode_strictMono m).monotone (Fin.le_last i)





theorem abs_eval_monicScaledChebyshev_chebPeak (m : ℕ) (i : Fin (m + 1)) :
    |(monicScaledChebyshev (m + 2)).eval (chebPeak m i)| = comparisonBound (m + 2) := by
  have hn : 2 ≤ m + 2 := Nat.le_add_left 2 m
  have hr := endpointScale_pos' m
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eval_monicScaledChebyshev hn, abs_mul]
  have hx : endpointScale (m + 2) * chebPeak m i
      = Real.cos (((m + 1 - (i : ℕ) : ℕ) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ)) := by
    simp only [chebPeak]
    field_simp
  rw [hx]
  have hT : |(Polynomial.Chebyshev.T ℝ ((m + 2 : ℕ) : ℤ)).eval
      (Real.cos (((m + 1 - (i : ℕ) : ℕ) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ)))| = 1 := by
    refine (Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff (n := m + 2) (by omega) _).mpr ?_
    exact ⟨m + 1 - (i : ℕ), by omega, rfl⟩
  rw [hT, mul_one]
  rfl

theorem chebPeak_mem_gap (m : ℕ) (i : Fin (m + 1)) :
    chebNode m i.castSucc < chebPeak m i ∧ chebPeak m i < chebNode m i.succ := by
  have hr := endpointScale_pos' m
  have hilt := i.isLt
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hp : ((m - (i : ℕ) : ℕ) : ℝ) ≤ (m : ℝ) := by
    have h1 : (m - (i : ℕ) : ℕ) ≤ m := by omega
    exact_mod_cast h1
  have h1 : (m + 1 - ((i.castSucc : Fin (m + 2)) : ℕ) : ℕ) = (m - (i : ℕ)) + 1 := by
    simp only [Fin.val_castSucc]; omega
  have h2 : (m + 1 - ((i.succ : Fin (m + 2)) : ℕ) : ℕ) = m - (i : ℕ) := by
    simp only [Fin.val_succ]; omega
  have h3 : (m + 1 - (i : ℕ) : ℕ) = (m - (i : ℕ)) + 1 := by omega
  have hangle : (((m + 1 - (i : ℕ) : ℕ)) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ)
      = (2 * ((m - (i : ℕ) : ℕ) : ℝ) + 2) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)) := by
    rw [h3]
    push_cast
    field_simp
  have hpeak : chebPeak m i
      = Real.cos ((2 * ((m - (i : ℕ) : ℕ) : ℝ) + 2) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
        / endpointScale (m + 2) := by
    simp only [chebPeak]; rw [hangle]
  simp only [chebNode, h1, h2, hpeak]
  constructor
  · apply div_lt_div_of_pos_right _ hr
    exact cos_angle_lt (twoN_pos m) (by positivity) (by push_cast; linarith)
      (by push_cast; linarith)
  · apply div_lt_div_of_pos_right _ hr
    exact cos_angle_lt (twoN_pos m) (by positivity) (by push_cast; linarith)
      (by push_cast; linarith)

theorem mem_segment_collinear {base dir : ℂ} {a b s p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (hs : p * a + q * b = s) :
    base + dir * (s : ℂ) ∈ segment ℝ (base + dir * (a : ℂ)) (base + dir * (b : ℂ)) := by
  refine ⟨p, q, hp, hq, hpq, ?_⟩
  simp only [Complex.real_smul]
  rw [← hs]
  push_cast
  have hc : (p : ℂ) + (q : ℂ) = 1 := by rw [← Complex.ofReal_add, hpq]; norm_num
  linear_combination base * hc
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {R : ℝ} (hR : 0 < R) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((R * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((R * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((R * chebNode m k : ℝ) : ℂ))} (2 * R) ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((R * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((R * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖ = comparisonBound (m + 2) * R ^ (m + 2) := by
  constructor
  · constructor
    · refine ⟨Fin.last (m + 1), 0, ?_⟩
      rw [dist_collinear _ _ hdir, chebNode_last, chebNode_zero,
        show R * 1 - R * (-1) = 2 * R by ring, abs_of_pos (by linarith)]
    · rintro d ⟨j, k, rfl⟩
      rw [dist_collinear _ _ hdir]
      have hcj := chebNode_abs_le m j
      have hck := chebNode_abs_le m k
      rw [abs_le] at hcj hck
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_nonneg hR.le (show (0 : ℝ) ≤ chebNode m j + 1 by linarith [hcj.1]),
          mul_nonneg hR.le (show (0 : ℝ) ≤ 1 - chebNode m k by linarith [hck.2])]
      · nlinarith [mul_nonneg hR.le (show (0 : ℝ) ≤ 1 - chebNode m j by linarith [hcj.2]),
          mul_nonneg hR.le (show (0 : ℝ) ≤ chebNode m k + 1 by linarith [hck.1])]
  · intro i
    obtain ⟨hg1, hg2⟩ := chebPeak_mem_gap m i
    refine ⟨base + dir * ((R * chebPeak m i : ℝ) : ℂ), ?_, ?_⟩
    · obtain ⟨A, hA⟩ : ∃ A : ℝ, A = R * chebNode m i.castSucc := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : ℝ, B = R * chebNode m i.succ := ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S : ℝ, S = R * chebPeak m i := ⟨_, rfl⟩
      have hAS : A ≤ S := by
        rw [hA, hS]; exact mul_le_mul_of_nonneg_left hg1.le hR.le
      have hSB : S ≤ B := by
        rw [hS, hB]; exact mul_le_mul_of_nonneg_left hg2.le hR.le
      have hAB : A < B := by
        rw [hA, hB]; exact mul_lt_mul_of_pos_left (lt_trans hg1 hg2) hR
      have hBA : B - A ≠ 0 := ne_of_gt (sub_pos.mpr hAB)
      rw [← hA, ← hB, ← hS]
      refine mem_segment_collinear (p := (B - S) / (B - A)) (q := (S - A) / (B - A))
        (div_nonneg (by linarith) (by linarith))
        (div_nonneg (by linarith) (by linarith)) ?_ ?_
      · rw [← add_div, show B - S + (S - A) = B - A by ring]
        exact div_self hBA
      · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hBA]
        ring
    · rw [norm_eval_collinear base dir hdir (fun k => R * chebNode m k) f hf
        (R * chebPeak m i)]
      have hsplit : ∀ k : Fin (m + 2),
          R * chebPeak m i - R * chebNode m k = R * (chebPeak m i - chebNode m k) := by
        intro k; ring
      rw [Finset.prod_congr rfl fun k _ => hsplit k, Finset.prod_mul_distrib]
      have hev : (∏ k : Fin (m + 2), (chebPeak m i - chebNode m k))
          = (monicScaledChebyshev (m + 2)).eval (chebPeak m i) := by
        rw [monicScaledChebyshev_eq_prod, eval_prod]
        simp
      rw [hev]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [abs_mul, abs_of_pos (pow_pos hR (m + 2)),
        abs_eval_monicScaledChebyshev_chebPeak]
      ring

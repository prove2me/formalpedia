-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T04:07:20.485265+00:00
-- url     : https://prove2.me/submissions/614e1da7-43ba-4fb8-9621-d022975fe0f5

import Definitions.Def_ErdosProblems_Erdos1041_SharpCollinearChebyshev
import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Theorems.Thm_ErdosProblems_Erdos1041_SharpCollinearChebyshev_endpointScale_pos
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_exists_gap_le_comparisonBound
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

/-- The tree's `comparisonBound` is the paper's `C_n`. -/
theorem comparisonBound_eq_inv {n : ℕ} (hn : 2 ≤ n) :
    comparisonBound n = (2 ^ (n - 1) * endpointScale n ^ n)⁻¹ := by
  have hr : 0 < endpointScale n := endpointScale_pos hn
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n :=
    mul_pos (by positivity) (pow_pos (inv_pos.mpr hr) n)
  show |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
      = (2 ^ (n - 1) * endpointScale n ^ n)⁻¹
  rw [abs_of_pos hpos, inv_pow, mul_inv]

/-- `comparisonBound n` written exactly as the paper's `C_n`. -/
theorem comparisonBound_eq {n : ℕ} (hn : 2 ≤ n) :
    comparisonBound n = 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) := by
  rw [comparisonBound_eq_inv hn, one_div]
  rfl

theorem comparisonBound_pos {n : ℕ} (hn : 2 ≤ n) : 0 < comparisonBound n := by
  have hr : 0 < endpointScale n := endpointScale_pos hn
  rw [comparisonBound_eq_inv hn]
  have : (0 : ℝ) < 2 ^ (n - 1) * endpointScale n ^ n :=
    mul_pos (by positivity) (pow_pos hr n)
  exact inv_pos.mpr this



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

theorem segment_collinear {base dir : ℂ} {a b : ℝ} {z : ℂ}
    (hz : z ∈ segment ℝ (base + dir * (a : ℂ)) (base + dir * (b : ℂ))) :
    ∃ s ∈ Icc (min a b) (max a b), z = base + dir * (s : ℂ) := by
  obtain ⟨p, r, hp, hr, hpr, hzeq⟩ := hz
  refine ⟨p * a + r * b, ⟨?_, ?_⟩, ?_⟩
  · have h1 : min a b ≤ a := min_le_left a b
    have h2 : min a b ≤ b := min_le_right a b
    have e1 : p * min a b ≤ p * a := mul_le_mul_of_nonneg_left h1 hp
    have e2 : r * min a b ≤ r * b := mul_le_mul_of_nonneg_left h2 hr
    have e3 : p * min a b + r * min a b = min a b := by rw [← add_mul, hpr, one_mul]
    linarith
  · have h1 : a ≤ max a b := le_max_left a b
    have h2 : b ≤ max a b := le_max_right a b
    have e1 : p * a ≤ p * max a b := mul_le_mul_of_nonneg_left h1 hp
    have e2 : r * b ≤ r * max a b := mul_le_mul_of_nonneg_left h2 hr
    have e3 : p * max a b + r * max a b = max a b := by rw [← add_mul, hpr, one_mul]
    linarith
  · rw [← hzeq]
    simp only [Complex.real_smul]
    push_cast
    have : (p : ℂ) + (r : ℂ) = 1 := by
      rw [← Complex.ofReal_add, hpr]; norm_num
    linear_combination base * this



/-! ### The sharp collinear root-diameter theorem -/
end ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev
open ErdosProblems.Erdos1041.PaperCompleteR21 in
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (base dir : ℂ) (hdir : ‖dir‖ = 1) (y : Fin n → ℝ) (f : ℂ[X])
    (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ)))) (D : ℝ)
    (hD : IsGreatest {d : ℝ | ∃ j k : Fin n,
        d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D) :
    ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
      (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
      dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
      ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
        ‖f.eval z‖
          ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) * (D / 2) ^ n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [← comparisonBound_eq hn]
  have hCpos : 0 < comparisonBound (m + 2) := comparisonBound_pos hn
  have hDnn : (0 : ℝ) ≤ D :=
    hD.2 (show (0 : ℝ) ∈ _ from ⟨0, 0, by simp⟩)
  by_cases hinj : Function.Injective y
  · -- distinct zeros: the Chebyshev comparison
    obtain ⟨w, hwSM, hwrange⟩ :
        ∃ w : Fin (m + 2) → ℝ, StrictMono w ∧ Set.range w = Set.range y := by
      have hcard : (Finset.image y Finset.univ).card = m + 2 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      refine ⟨(Finset.image y Finset.univ).orderEmbOfFin hcard,
        OrderEmbedding.strictMono _, ?_⟩
      rw [Finset.range_orderEmbOfFin, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hwinj : Function.Injective w := hwSM.injective
    have hwy : ∀ a : Fin (m + 2), ∃ l, y l = w a := by
      intro a
      have h : w a ∈ Set.range y := by rw [← hwrange]; exact Set.mem_range_self a
      exact h
    have hyw : ∀ l : Fin (m + 2), ∃ a, y l = w a := by
      intro l
      have h : y l ∈ Set.range w := by rw [hwrange]; exact Set.mem_range_self l
      obtain ⟨a, ha⟩ := h
      exact ⟨a, ha.symm⟩
    have hw0le : ∀ l, w 0 ≤ y l := by
      intro l; obtain ⟨a, ha⟩ := hyw l; rw [ha]; exact hwSM.monotone (Fin.zero_le a)
    have hwlastge : ∀ l, y l ≤ w (Fin.last (m + 1)) := by
      intro l; obtain ⟨a, ha⟩ := hyw l; rw [ha]; exact hwSM.monotone (Fin.le_last a)
    have hwlt : w 0 < w (Fin.last (m + 1)) :=
      hwSM (by rw [Fin.lt_def]; simp only [Fin.val_zero, Fin.val_last]; omega)
    have hne : w (Fin.last (m + 1)) - w 0 ≠ 0 := ne_of_gt (sub_pos.mpr hwlt)
    have hDeq : D = w (Fin.last (m + 1)) - w 0 := by
      refine hD.unique ⟨?_, ?_⟩
      · obtain ⟨l1, hl1⟩ := hwy (Fin.last (m + 1))
        obtain ⟨l0, hl0⟩ := hwy 0
        exact ⟨l1, l0, by
          rw [dist_collinear _ _ hdir, hl1, hl0, abs_of_nonneg (by linarith)]⟩
      · rintro d ⟨j, k, rfl⟩
        rw [dist_collinear _ _ hdir, abs_le]
        constructor
        · linarith [hwlastge k, hw0le j]
        · linarith [hwlastge j, hw0le k]
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (w (Fin.last (m + 1)) - w 0) / 2 := ⟨_, rfl⟩
    obtain ⟨mid, hmiddef⟩ : ∃ mid : ℝ, mid = (w 0 + w (Fin.last (m + 1))) / 2 := ⟨_, rfl⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y : Fin (m + 2) → ℝ, ∀ a, Y a = (w a - mid) / R :=
      ⟨_, fun _ => rfl⟩
    have hRpos : 0 < R := by rw [hRdef]; linarith
    have hYSM : StrictMono Y := by
      intro a b hab
      rw [hYdef, hYdef]
      exact div_lt_div_of_pos_right (by linarith [hwSM hab]) hRpos
    have hY0 : Y 0 = -1 := by
      rw [hYdef, hmiddef, hRdef]; field_simp; try ring
    have hY1 : Y (Fin.last (m + 1)) = 1 := by
      rw [hYdef, hmiddef, hRdef]; field_simp; try ring
    obtain ⟨i, hi⟩ := exists_gap_le_comparisonBound Y hYSM hY0 hY1
    obtain ⟨j, hj⟩ := hwy i.castSucc
    obtain ⟨k, hk⟩ := hwy i.succ
    have hwij : w i.castSucc < w i.succ := hwSM i.castSucc_lt_succ
    refine ⟨j, k, ?_, ?_, ?_, ?_, ?_⟩
    · intro hEq; rw [hEq, hk] at hj; linarith
    · rw [hj, hk]; exact hwij.le
    · intro l
      obtain ⟨a, ha⟩ := hyw l
      rcases Nat.lt_or_ge (i : ℕ) (a : ℕ) with h | h
      · exact Or.inr (by
          rw [ha, hk]
          exact hwSM.monotone (by rw [Fin.le_def, Fin.val_succ]; omega))
      · exact Or.inl (by
          rw [ha, hj]
          exact hwSM.monotone (by rw [Fin.le_def, Fin.val_castSucc]; omega))
    · rw [dist_collinear _ _ hdir, hj, hk, abs_of_nonpos (by linarith), hDeq]
      have h1 : w 0 ≤ w i.castSucc := hwSM.monotone (Fin.zero_le _)
      have h2 : w i.succ ≤ w (Fin.last (m + 1)) := hwSM.monotone (Fin.le_last _)
      linarith
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := segment_collinear hz
      rw [norm_eval_collinear base dir hdir y f hf s]
      have himgy : Finset.image y Finset.univ = Finset.image w Finset.univ := by
        apply Finset.coe_injective
        rw [Finset.coe_image, Finset.coe_image, Finset.coe_univ, Set.image_univ,
          Set.image_univ, hwrange]
      have hpy : ∏ t ∈ Finset.image y Finset.univ, (s - t) = ∏ l, (s - y l) :=
        Finset.prod_image (fun x _ x' _ h => hinj h)
      have hpw : ∏ t ∈ Finset.image w Finset.univ, (s - t) = ∏ a, (s - w a) :=
        Finset.prod_image (fun x _ x' _ h => hwinj h)
      have hreindex : (∏ l, (s - y l)) = ∏ a, (s - w a) := by
        rw [← hpy, ← hpw, himgy]
      have hscale : ∀ a, s - w a = R * ((s - mid) / R - Y a) := by
        intro a; rw [hYdef]; field_simp; ring
      have hprod : (∏ a, (s - w a)) = R ^ (m + 2) * ∏ a, ((s - mid) / R - Y a) := by
        rw [Finset.prod_congr rfl fun a _ => hscale a, Finset.prod_mul_distrib]
        simp
      have hsmem : w i.castSucc ≤ s ∧ s ≤ w i.succ := by
        rw [hj, hk, min_eq_left hwij.le, max_eq_right hwij.le] at hs
        exact ⟨hs.1, hs.2⟩
      have hdiff1 : (s - mid) / R - Y i.castSucc = (s - w i.castSucc) / R := by
        rw [hYdef]; field_simp; ring
      have hdiff2 : Y i.succ - (s - mid) / R = (w i.succ - s) / R := by
        rw [hYdef]; field_simp; ring
      have hx : (s - mid) / R ∈ Icc (Y i.castSucc) (Y i.succ) := by
        constructor
        · have h := div_nonneg (sub_nonneg.mpr hsmem.1) hRpos.le
          rw [← hdiff1] at h; linarith
        · have h := div_nonneg (sub_nonneg.mpr hsmem.2) hRpos.le
          rw [← hdiff2] at h; linarith
      have hbound := hi _ hx
      have hRD : R = D / 2 := by rw [hRdef, hDeq]
      rw [hreindex, hprod, abs_mul, abs_of_pos (pow_pos hRpos (m + 2))]
      calc R ^ (m + 2) * |∏ a, ((s - mid) / R - Y a)|
          ≤ R ^ (m + 2) * comparisonBound (m + 2) :=
            mul_le_mul_of_nonneg_left hbound (pow_pos hRpos _).le
        _ = comparisonBound (m + 2) * (D / 2) ^ (m + 2) := by rw [hRD]; ring
  · -- a repeated zero occurrence: the constant path
    obtain ⟨j, k, h1, h2⟩ := Function.not_injective_iff.mp hinj
    refine ⟨j, k, h2, le_of_eq h1, ?_, ?_, ?_⟩
    · intro l
      rcases le_total (y l) (y j) with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← h1]; exact h)
    · rw [dist_collinear _ _ hdir, h1, sub_self, abs_zero]; exact hDnn
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := segment_collinear hz
      have hsj : s = y j := by
        rw [← h1, min_self, max_self] at hs
        exact le_antisymm hs.2 hs.1
      rw [norm_eval_collinear base dir hdir y f hf s, hsj,
        Finset.prod_eq_zero (Finset.mem_univ j) (by ring), abs_zero]
      exact mul_nonneg hCpos.le (pow_nonneg (by linarith) _)

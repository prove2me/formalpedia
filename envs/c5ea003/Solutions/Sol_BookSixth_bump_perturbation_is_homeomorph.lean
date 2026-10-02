-- Prove2me | solution 1 for BookSixth.bump_perturbation_is_homeomorph
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-27T08:39:54.267641+00:00
-- url     : https://prove2.me/submissions/12614976-632e-42c3-ab6b-77612f57d866

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

noncomputable section

-- `BookSixth.bump_perturbation_is_homeomorph` is false. Its hypotheses bound each
-- displacement `S i x - x` by `q < 1` and each cut-off `chi i` by `L`, but nothing
-- bounds the product of the two, and nothing requires the perturbations to be
-- distinct. Two identical translations already fold the first coordinate.
--
-- Take `n = 2`, `L = 1`, `q = 3/4`, and let `cl t = max (-1) (min 1 t)`. Put
-- `e = ![1,0,0]` and `d = (3/4) e`. Choose `chi i x = - cl (x 0)` and
-- `S i x = x + d` for both indices. Then
--     F x = x + sum_i, chi i x * (S i x - x) = x - (3/2) cl (x 0) * e,
-- so the first coordinate of `F` is `g t = t - (3/2) cl t`. Since
-- `g (-1) = -1 + 3/2 = 1/2` and `g 2 = 2 - 3/2 = 1/2`, the distinct points
-- `![-1,0,0]` and `![2,0,0]` have the same image, so `F` is not injective and the
-- required `Finv` cannot exist.

def cl (t : ℝ) : ℝ := max (-1 : ℝ) (min 1 t)

theorem cl_lip : LipschitzWith 1 (cl : ℝ → ℝ) :=
  ((LipschitzWith.id.const_min 1).const_max (-1))

theorem cl_cont : Continuous cl := LipschitzWith.continuous cl_lip

theorem cl_bound (t : ℝ) : |cl t| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

-- The witness data. Both `S i` are the same translation, so `hS` and `hcont` are
-- immediate; both `chi i` are `-cl (x 0)`.
def dvec : Space3 := (3 / 4 : ℝ) • (![1, 0, 0] : Fin 3 → ℝ)

def badS (_i : Fin 2) (x : Space3) : Space3 := x + dvec

def badChi (_i : Fin 2) (x : Space3) : ℝ := -cl (x 0)

theorem badS_lip (i : Fin 2) : LipschitzWith 1 (badS i) := by
  intro x y
  have h := dist_vadd_cancel_left dvec x y
  simpa [badS, add_comm] using h

theorem badS_cont (i : Fin 2) : Continuous (badS i) := by
  unfold badS
  fun_prop

theorem eval_lip : LipschitzWith 1 (fun x : Space3 => x 0) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    have h : dist (a 0) (b 0) = ‖(a - b) (0 : Fin 3)‖ := by
      rw [dist_eq_norm]; rfl
    rw [h, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_le_pi_norm (a - b) (0 : Fin 3)

theorem badChi_lip (i : Fin 2) : LipschitzWith 1 (badChi i) := by
  unfold badChi
  simpa only [Pi.neg_apply, one_mul] using (cl_lip.comp eval_lip).neg

theorem badChi_cont (i : Fin 2) : Continuous (badChi i) := by
  have hx : Continuous (fun x : Space3 => x 0) := LipschitzWith.continuous eval_lip
  have hcomp : Continuous (cl ∘ (fun x : Space3 => x 0)) := cl_cont.comp hx
  simpa [badChi, Function.comp_def] using hcomp.neg

theorem badChi_bound (i : Fin 2) (x : Space3) : ‖badChi i x‖ ≤ 1 := by
  rw [badChi, Real.norm_eq_abs, abs_neg]
  exact cl_bound (x 0)

-- The sum collapses because the two summands are identical.
theorem F_form (x : Space3) :
    (∑ i : Fin 2, badChi i x • (badS i x - x))
      = (2 : ℝ) • (badChi 0 x • dvec) := by
  have h : ∀ i : Fin 2, badChi i x • (badS i x - x) = badChi 0 x • dvec := by
    intro i
    simp [badChi, badS, dvec]
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp only [dvec, badChi, smul_eq_mul, Pi.sub_apply, Fin.sum_univ_two,
    Pi.add_apply, Pi.zero_apply, one_smul, Finset.card_fin, Finset.sum_const, nsmul_eq_mul]
  funext i
  fin_cases i <;> simp <;> ring

/-- The value of `F` forced by the witness: the first coordinate is
`t - (3/2) cl t`, the others are unchanged. -/
theorem F_val (x : Space3) :
    x + ∑ i : Fin 2, badChi i x • (badS i x - x)
      = x - ((3 / 2 : ℝ) * cl (x 0)) • (![1, 0, 0] : Fin 3 → ℝ) := by
  rw [F_form]
  simp only [badChi, dvec, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
  funext i
  fin_cases i <;> simp <;> ring

theorem F_val_neg : (![-1, 0, 0] : Fin 3 → ℝ) + (∑ i : Fin 2, badChi i (![-1, 0, 0]) •
    (badS i (![-1, 0, 0]) - ![-1, 0, 0])) = (![1 / 2, 0, 0] : Fin 3 → ℝ) := by
  rw [F_val]
  have hz : (![-1, 0, 0] : Fin 3 → ℝ) 0 = -1 := rfl
  have h1 : cl (-1) = -1 := by simp [cl]
  rw [hz, h1]
  funext i
  fin_cases i <;> simp <;> ring

theorem F_val_two : (![2, 0, 0] : Fin 3 → ℝ) + (∑ i : Fin 2, badChi i (![2, 0, 0]) •
    (badS i (![2, 0, 0]) - ![2, 0, 0])) = (![1 / 2, 0, 0] : Fin 3 → ℝ) := by
  rw [F_val]
  have hz : (![2, 0, 0] : Fin 3 → ℝ) 0 = 2 := rfl
  have h1 : cl 2 = 1 := by simp [cl]
  rw [hz, h1]
  funext i
  fin_cases i <;> simp <;> ring

-- The disproof.  The `theorem solution` statement is the NEGATION of the target,
-- which is the contract for a `disprove` submission: assume the conclusion, then
-- instantiate it with the witness data and derive a contradiction.
theorem solution : ¬ (∀ (n : ℕ) (L : ℝ) (hL : 0 ≤ L) (q : ℝ), 0 ≤ q ∧ q < 1 →
    ∀ (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3),
      (∀ i, LipschitzWith 1 (chi i)) → (∀ i x, ‖chi i x‖ ≤ L) →
      (∀ i, LipschitzWith 1 (S i)) → (∀ i x, ‖S i x - x‖ ≤ q) →
      (∀ i, Continuous (S i)) → (∀ i, Continuous (chi i)) →
      ∃ F : Space3 → Space3, Continuous F ∧ ∃ Finv : Space3 → Space3, Continuous Finv ∧
        ∀ x, Finv (F x) = x ∧ ∀ x, F (Finv x) = x ∧
          ∀ x, F x = x + ∑ i, chi i x • (S i x - x)) := by
  intro hall
  obtain ⟨F, hFcont, Finv, hFinvcont, hrest⟩ :=
    hall 2 1 (by norm_num) (3 / 4) (by norm_num) badChi badS
      (fun i => badChi_lip i) (fun i x => badChi_bound i x)
      (fun i => badS_lip i) (fun i x => by
        have hd : badS i x - x = dvec := by simp [badS]
        rw [hd, dvec, norm_smul, Real.norm_eq_abs]
        have hb : ‖(![1, 0, 0] : Fin 3 → ℝ)‖ ≤ (1 : ℝ) := by
          refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun i => ?_)
          fin_cases i <;> simp
        calc |3 / 4| * ‖(![1, 0, 0] : Fin 3 → ℝ)‖ ≤ |3 / 4| * 1 :=
              mul_le_mul_of_nonneg_left hb (by norm_num)
          _ = 3 / 4 := by norm_num)
      (fun i => badS_cont i) (fun i => badChi_cont i)
  -- `hrest x` is `A x ∧ ∀ y, B y ∧ C y`: the two inner clauses are themselves
  -- right-nested `And`s under one further `∀`, so each needs an extra application.
  have hhl : ∀ x, Finv (F x) = x := fun x => (hrest x).1
  have hform : ∀ x, F x = x + ∑ i, badChi i x • (badS i x - x) := fun x => ((hrest x).2 x).2 x
  have e1 : F (![-1, 0, 0] : Fin 3 → ℝ) = ![1 / 2, 0, 0] := by
    rw [hform]; exact F_val_neg
  have e2 : F (![2, 0, 0] : Fin 3 → ℝ) = ![1 / 2, 0, 0] := by
    rw [hform]; exact F_val_two
  have h12 : (![-1, 0, 0] : Fin 3 → ℝ) = ![2, 0, 0] := calc
    (![-1, 0, 0] : Fin 3 → ℝ) = Finv (F (![-1, 0, 0] : Fin 3 → ℝ)) := (hhl _).symm
    _ = Finv (F (![2, 0, 0] : Fin 3 → ℝ)) := by rw [e2, e1]
    _ = ![2, 0, 0] := hhl _
  refine absurd h12 ?_
  intro hh
  have e : (![-1, 0, 0] : Fin 3 → ℝ) 0 = (![2, 0, 0] : Fin 3 → ℝ) 0 :=
    congrArg (fun v : Fin 3 → ℝ => v 0) hh
  norm_num [Fin.cons_zero, Matrix.head_cons] at e

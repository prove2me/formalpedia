-- Prove2me | solution 1 for MarkovMixing.hypercube_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T07:07:48.800724+00:00
-- url     : https://prove2.me/submissions/7938008e-67d0-499c-84fd-e76112873ba0

import Definitions.Def_mm_cutoff
import Definitions.Def_mm_lower
import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Theorems.Thm_MarkovMixing_hypercube_lower_bound
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cutoff for the lazy walk on the hypercube (LPW Theorem 18.3)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Hypercube

variable {n : ℕ}

/-- Flip the `j`-th coordinate. -/
private def flp (x : Fin n → ZMod 2) (j : Fin n) : Fin n → ZMod 2 :=
  Function.update x j (x j + 1)

private lemma flp_apply (x : Fin n → ZMod 2) (j i : Fin n) :
    flp x j i = if i = j then x j + 1 else x i := by
  simp only [flp, Function.update_apply]

private lemma flp_ne (x : Fin n → ZMod 2) (j : Fin n) : flp x j ≠ x := by
  intro hc
  have := congrFun hc j
  rw [flp_apply, if_pos rfl] at this
  revert this
  generalize x j = a
  revert a
  decide

private lemma flp_inj (x : Fin n → ZMod 2) : Function.Injective (flp x) := by
  intro i j h
  by_contra hij
  have h1 := congrFun h i
  rw [flp_apply, flp_apply, if_pos rfl, if_neg hij] at h1
  revert h1
  generalize x i = a
  revert a
  decide

private lemma adj_iff (x y : Fin n → ZMod 2) :
    (torusGraph n 2).Adj x y ↔ ∃ j, y = flp x j := by
  constructor
  · rintro ⟨hxy, j, hoff, hj⟩
    refine ⟨j, ?_⟩
    funext i
    rw [flp_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hm : (-1 : ZMod 2) = 1 := by decide
      rcases hj with h | h
      · exact h
      · rw [h, sub_eq_add_neg, hm]
    · rw [if_neg hij]
      exact (hoff i hij).symm
  · rintro ⟨j, rfl⟩
    refine ⟨(flp_ne x j).symm, j, ?_, ?_⟩
    · intro i hi
      rw [flp_apply, if_neg hi]
    · left
      rw [flp_apply, if_pos rfl]


private lemma nbr_eq (x : Fin n → ZMod 2) :
    (torusGraph n 2).neighborFinset x = Finset.univ.image (flp x) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
  rw [adj_iff]
  exact ⟨fun ⟨j, hj⟩ => ⟨j, hj.symm⟩, fun ⟨j, hj⟩ => ⟨j, hj.symm⟩⟩

private lemma deg_eq (x : Fin n → ZMod 2) : (torusGraph n 2).degree x = n := by
  rw [SimpleGraph.degree, nbr_eq, Finset.card_image_of_injective _ (flp_inj x),
    Finset.card_univ, Fintype.card_fin]

private lemma hc_step (f : (Fin n → ZMod 2) → ℝ) (x : Fin n → ZMod 2) :
    ∑ y, hypercubeWalk n x y * f y
      = 2⁻¹ * f x + (2⁻¹ * ((n : ℝ))⁻¹) * ∑ j : Fin n, f (flp x j) := by
  classical
  have hzero : ∀ y ∈ (Finset.univ : Finset (Fin n → ZMod 2)),
      y ∉ (torusGraph n 2).neighborFinset x →
      graphWalk (torusGraph n 2) x y * f y = 0 := by
    intro y _ hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    simp only [graphWalk, if_neg hy, zero_mul]
  have hg : ∑ y, graphWalk (torusGraph n 2) x y * f y
      = ((n : ℝ))⁻¹ * ∑ j : Fin n, f (flp x j) := by
    rw [← Finset.sum_subset (Finset.subset_univ ((torusGraph n 2).neighborFinset x)) hzero,
      nbr_eq, Finset.sum_image (fun a _ b _ h => flp_inj x h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hadj : (torusGraph n 2).Adj x (flp x j) := (adj_iff x (flp x j)).mpr ⟨j, rfl⟩
    simp only [graphWalk, if_pos hadj, deg_eq]
  have hone : ∑ y, (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ) x y * f y = f x := by
    simp [Matrix.one_apply, Finset.sum_ite_eq]
  simp only [hypercubeWalk, lazy, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun y _ => by ring :
      ∀ y ∈ Finset.univ, (2 : ℝ)⁻¹ * (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ) x y * f y
        = 2⁻¹ * ((1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ) x y * f y)),
    Finset.sum_congr rfl (fun y _ => by ring :
      ∀ y ∈ Finset.univ, (2 : ℝ)⁻¹ * graphWalk (torusGraph n 2) x y * f y
        = 2⁻¹ * (graphWalk (torusGraph n 2) x y * f y)),
    ← Finset.mul_sum, ← Finset.mul_sum, hone, hg]
  ring

end Hypercube

/-! ### Walsh characters -/

section Characters

variable {n : ℕ}

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private lemma zmod2_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

private def ee (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

private lemma ee_zero : ee 0 = 1 := by simp [ee]

private lemma ee_one : ee 1 = -1 := by
  have : (1 : ZMod 2) ≠ 0 := by decide
  simp [ee, this]

private lemma ee_add (a b : ZMod 2) : ee (a + b) = ee a * ee b := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;> subst ha <;>
    subst hb
  · rw [add_zero, ee_zero]; ring
  · rw [zero_add, ee_zero]; ring
  · rw [add_zero, ee_zero]; ring
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide, ee_zero, ee_one]; ring

private lemma ee_sq (a : ZMod 2) : ee a * ee a = 1 := by
  rcases zmod2_cases a with ha | ha <;> subst ha
  · rw [ee_zero]; ring
  · rw [ee_one]; ring

private lemma sum_prod_zmod2 (g : Fin n → ZMod 2 → ℝ) :
    ∑ x : Fin n → ZMod 2, ∏ i : Fin n, g i (x i) = ∏ i : Fin n, (∑ a : ZMod 2, g i a) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))
    (fun (i : Fin n) (a : ZMod 2) => g i a)
  rw [Fintype.piFinset_univ] at h
  exact h.symm

/-- The Walsh character `χ_S(x) = (-1)^{⟨S,x⟩}`. -/
private def chi (S x : Fin n → ZMod 2) : ℝ := ∏ i, ee (S i * x i)

private lemma chi_symm (S x : Fin n → ZMod 2) : chi S x = chi x S :=
  Finset.prod_congr rfl fun i _ => by rw [mul_comm]

private lemma chi_add (S x y : Fin n → ZMod 2) : chi S (x + y) = chi S x * chi S y := by
  simp only [chi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : S i * (x + y) i = S i * x i + S i * y i := by
    simp only [Pi.add_apply]; ring
  rw [h, ee_add]

private lemma chi_sq (S x : Fin n → ZMod 2) : chi S x * chi S x = 1 := by
  simp only [chi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => ee_sq _

private lemma chi_zero_left (x : Fin n → ZMod 2) : chi 0 x = 1 :=
  Finset.prod_eq_one fun i _ => by simp only [Pi.zero_apply, zero_mul, ee_zero]

private lemma chi_sum (S : Fin n → ZMod 2) :
    ∑ x : Fin n → ZMod 2, chi S x = if S = 0 then 2 ^ n else 0 := by
  classical
  have hfac : ∀ i : Fin n, (∑ a : ZMod 2, ee (S i * a)) = if S i = 0 then 2 else 0 := by
    intro i
    rw [zmod2_univ, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), mul_zero, mul_one, ee_zero]
    rcases zmod2_cases (S i) with h | h <;> rw [h]
    · rw [if_pos rfl, ee_zero]; norm_num
    · rw [if_neg (by decide : (1 : ZMod 2) ≠ 0), ee_one]; norm_num
  rw [show (∑ x : Fin n → ZMod 2, chi S x)
      = ∑ x : Fin n → ZMod 2, ∏ i : Fin n, ee (S i * x i) from rfl,
    sum_prod_zmod2 (fun i a => ee (S i * a)),
    Finset.prod_congr rfl (fun i _ => hfac i)]
  by_cases hS : S = 0
  · subst hS
    rw [if_pos rfl, Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      by simp : ∀ i ∈ Finset.univ, (if (0 : Fin n → ZMod 2) i = 0 then (2:ℝ) else 0) = 2),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ : ∃ i, S i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hS (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [if_neg hi]

end Characters

/-! ### The spectral decomposition of the hypercube walk -/

section Spectral

variable {n : ℕ}

private def wt (S : Fin n → ZMod 2) : ℕ := (Finset.univ.filter fun i => S i = 1).card

private def lamS (n : ℕ) (S : Fin n → ZMod 2) : ℝ := 1 - (wt S : ℝ) / n

private lemma sum_ee (S : Fin n → ZMod 2) :
    ∑ j : Fin n, ee (S j) = (n : ℝ) - 2 * (wt S : ℝ) := by
  classical
  have hcard : (Finset.univ.filter (fun i : Fin n => S i = 1)).card
      + (Finset.univ.filter (fun i : Fin n => ¬ (S i = 1))).card = n := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
  have h1 : ∑ j ∈ Finset.univ.filter (fun i : Fin n => S i = 1), ee (S j) = -(wt S : ℝ) := by
    rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2, ee_one]),
      Finset.sum_const, nsmul_eq_mul, wt]
    ring
  have h2 : ∑ j ∈ Finset.univ.filter (fun i : Fin n => ¬ (S i = 1)), ee (S j)
      = ((Finset.univ.filter (fun i : Fin n => ¬ (S i = 1))).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rcases zmod2_cases (S j) with h | h
      · rw [h, ee_zero]
      · exact absurd h (Finset.mem_filter.mp hj).2), Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc2 : ((Finset.univ.filter (fun i : Fin n => ¬ (S i = 1))).card : ℝ)
      = (n : ℝ) - (wt S : ℝ) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hcard
    push_cast at this
    rw [wt]
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => S i = 1), h1, h2, hc2]
  ring

private lemma chi_flp (S x : Fin n → ZMod 2) (j : Fin n) :
    chi S (flp x j) = chi S x * ee (S j) := by
  classical
  simp only [chi]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
    ← Finset.prod_erase_mul Finset.univ (fun i => ee (S i * x i)) (Finset.mem_univ j)]
  have hprod : ∏ i ∈ Finset.univ.erase j, ee (S i * flp x j i)
      = ∏ i ∈ Finset.univ.erase j, ee (S i * x i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [flp_apply, if_neg (Finset.mem_erase.mp hi).1]
  have hlast : ee (S j * flp x j j) = ee (S j * x j) * ee (S j) := by
    rw [flp_apply, if_pos rfl, mul_add, mul_one, ee_add]
  rw [hprod, hlast]
  ring

private lemma chi_eigen (hn : 1 ≤ n) (S x : Fin n → ZMod 2) :
    ∑ y, hypercubeWalk n x y * chi S y = lamS n S * chi S x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hc_step (chi S) x, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => chi_flp S x j),
    ← Finset.mul_sum, sum_ee, lamS]
  field_simp
  ring

private lemma add_eq_zero_iff' (x y : Fin n → ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    revert hi
    generalize x i = a
    generalize y i = b
    revert a b
    decide
  · rintro rfl
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize x i = a
    revert a
    decide

private lemma pow_formula (hn : 1 ≤ n) : ∀ (t : ℕ) (x y : Fin n → ZMod 2),
    ((hypercubeWalk n) ^ t) x y
      = ((2 : ℝ) ^ n)⁻¹ * ∑ S : Fin n → ZMod 2, chi S x * chi S y * (lamS n S) ^ t := by
  intro t
  induction t with
  | zero =>
      intro x y
      rw [pow_zero, Matrix.one_apply]
      simp only [pow_zero, mul_one]
      rw [Finset.sum_congr rfl (fun S (_ : S ∈ Finset.univ) => by
        rw [← chi_add S x y, chi_symm] :
        ∀ S ∈ Finset.univ, chi S x * chi S y = chi (x + y) S), chi_sum (x + y)]
      by_cases hxy : x = y
      · rw [if_pos hxy, if_pos ((add_eq_zero_iff' x y).mpr hxy)]
        field_simp
      · rw [if_neg hxy, if_neg (fun hc => hxy ((add_eq_zero_iff' x y).mp hc)), mul_zero]
  | succ t ih =>
      intro x y
      have hstep : ((hypercubeWalk n) ^ (t + 1)) x y
          = ∑ w, hypercubeWalk n x w * ((hypercubeWalk n) ^ t) w y := by
        rw [pow_succ', Matrix.mul_apply]
      calc ((hypercubeWalk n) ^ (t + 1)) x y
          = ∑ w : Fin n → ZMod 2, ∑ S : Fin n → ZMod 2,
              ((2 : ℝ) ^ n)⁻¹ *
                (hypercubeWalk n x w * chi S w * (chi S y * (lamS n S) ^ t)) := by
            rw [hstep]
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [ih w y, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun S _ => by ring
        _ = ∑ S : Fin n → ZMod 2, ∑ w : Fin n → ZMod 2,
              ((2 : ℝ) ^ n)⁻¹ *
                (hypercubeWalk n x w * chi S w * (chi S y * (lamS n S) ^ t)) :=
            Finset.sum_comm
        _ = ((2 : ℝ) ^ n)⁻¹ *
              ∑ S : Fin n → ZMod 2, chi S x * chi S y * (lamS n S) ^ (t + 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [← Finset.mul_sum]
            congr 1
            rw [← Finset.sum_mul, chi_eigen hn S x, pow_succ]
            ring

end Spectral

/-! ### The `ℓ²` bound -/

section L2

variable {n : ℕ}

private lemma card_hc (n : ℕ) : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

private lemma wt_zero (n : ℕ) : wt (0 : Fin n → ZMod 2) = 0 := by
  rw [wt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  simp only [Pi.zero_apply]
  decide

private lemma lamS_zero (n : ℕ) : lamS n (0 : Fin n → ZMod 2) = 1 := by
  rw [lamS, wt_zero]
  norm_num

private lemma dev_eq (hn : 1 ≤ n) (t : ℕ) (x y : Fin n → ZMod 2) :
    ((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹
      = ((2 : ℝ) ^ n)⁻¹ * ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2),
          chi S x * chi S y * (lamS n S) ^ t := by
  rw [pow_formula hn t x y]
  have hsplit : ∑ S : Fin n → ZMod 2, chi S x * chi S y * (lamS n S) ^ t
      = (∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2), chi S x * chi S y * (lamS n S) ^ t)
        + chi (0 : Fin n → ZMod 2) x * chi (0 : Fin n → ZMod 2) y
            * (lamS n (0 : Fin n → ZMod 2)) ^ t :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
  rw [hsplit, chi_zero_left x, chi_zero_left y, lamS_zero, one_pow]
  ring

private lemma orth (S T : Fin n → ZMod 2) :
    (∑ y : Fin n → ZMod 2, chi S y * chi T y) = if S = T then (2 : ℝ) ^ n else 0 := by
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => by
      rw [chi_symm S y, chi_symm T y, ← chi_add, chi_symm] :
      ∀ y ∈ Finset.univ, chi S y * chi T y = chi (S + T) y), chi_sum (S + T)]
  by_cases h : S = T
  · rw [if_pos h, if_pos ((add_eq_zero_iff' S T).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((add_eq_zero_iff' S T).mp hc))]

private lemma l2_identity (hn : 1 ≤ n) (t : ℕ) (x : Fin n → ZMod 2) :
    ∑ y : Fin n → ZMod 2, (((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹) ^ 2
      = ((2 : ℝ) ^ n)⁻¹ *
          ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2), ((lamS n S) ^ t) ^ 2 := by
  classical
  set E : Finset (Fin n → ZMod 2) := Finset.univ.erase (0 : Fin n → ZMod 2) with hE
  set g : (Fin n → ZMod 2) → ℝ := fun S => chi S x * (lamS n S) ^ t with hg
  have hA : ∀ y : Fin n → ZMod 2,
      (((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹) ^ 2
        = (((2 : ℝ) ^ n)⁻¹) ^ 2 * ((∑ S ∈ E, g S * chi S y) * (∑ T ∈ E, g T * chi T y)) := by
    intro y
    rw [dev_eq hn t x y]
    have h1 : ∑ S ∈ E, chi S x * chi S y * (lamS n S) ^ t = ∑ S ∈ E, g S * chi S y :=
      Finset.sum_congr rfl fun S _ => by rw [hg]; ring
    rw [h1]
    ring
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hA y), ← Finset.mul_sum]
  have hexp : ∑ y : Fin n → ZMod 2,
        (∑ S ∈ E, g S * chi S y) * (∑ T ∈ E, g T * chi T y)
      = ∑ S ∈ E, ∑ T ∈ E, g S * g T * ∑ y : Fin n → ZMod 2, chi S y * chi T y := by
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) =>
      Finset.sum_mul_sum E E (fun S => g S * chi S y) (fun T => g T * chi T y))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hexp]
  have hin : ∀ S ∈ E, (∑ T ∈ E, g S * g T * ∑ y : Fin n → ZMod 2, chi S y * chi T y)
      = g S * g S * (2 : ℝ) ^ n := by
    intro S hS
    rw [Finset.sum_congr rfl (fun T (_ : T ∈ E) => by
        rw [orth S T, mul_ite, mul_zero] :
        ∀ T ∈ E, g S * g T * (∑ y : Fin n → ZMod 2, chi S y * chi T y)
          = if S = T then g S * g T * (2 : ℝ) ^ n else 0),
      Finset.sum_ite_eq E S (fun T => g S * g T * (2 : ℝ) ^ n), if_pos hS]
  rw [Finset.sum_congr rfl hin]
  have hgg : ∀ S ∈ E, g S * g S * (2 : ℝ) ^ n = (2 : ℝ) ^ n * ((lamS n S) ^ t) ^ 2 := by
    intro S _
    show (chi S x * (lamS n S) ^ t) * (chi S x * (lamS n S) ^ t) * (2:ℝ) ^ n
      = (2:ℝ) ^ n * ((lamS n S) ^ t) ^ 2
    linear_combination ((lamS n S) ^ t) ^ 2 * (2:ℝ) ^ n * (chi_sq S x)
  rw [Finset.sum_congr rfl hgg, ← Finset.mul_sum]
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  field_simp
  try ring

end L2

/-! ### From the `ℓ²` bound to total variation -/

section TV

variable {n : ℕ}

private lemma hc_nonneg (x y : Fin n → ZMod 2) : 0 ≤ hypercubeWalk n x y := by
  simp only [hypercubeWalk, lazy, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, graphWalk]
  have h1 : (0:ℝ) ≤ (if x = y then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have h2 : (0:ℝ) ≤ (if (torusGraph n 2).Adj x y then (((torusGraph n 2).degree x : ℝ))⁻¹ else 0) := by
    split_ifs
    · positivity
    · norm_num
  positivity

private lemma hc_stochastic (hn : 1 ≤ n) : IsStochastic (hypercubeWalk n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨hc_nonneg, fun x => ?_⟩
  have h := hc_step (fun _ => (1:ℝ)) x
  simp only [mul_one] at h
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  norm_num

private lemma hc_pow_nonneg (hn : 1 ≤ n) :
    ∀ (t : ℕ) (x y : Fin n → ZMod 2), 0 ≤ ((hypercubeWalk n) ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hc_nonneg z y)

private lemma hc_pow_sum (hn : 1 ≤ n) :
    ∀ (t : ℕ) (x : Fin n → ZMod 2), ∑ y, ((hypercubeWalk n) ^ t) x y = 1 := by
  intro t
  induction t with
  | zero => intro x; simp [Matrix.one_apply]
  | succ t ih =>
      intro x
      rw [Finset.sum_congr rfl fun y _ => by rw [pow_succ, Matrix.mul_apply], Finset.sum_comm]
      rw [Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm]
      rw [Finset.sum_congr rfl fun z _ => by rw [(hc_stochastic hn).2 z, mul_one]]
      exact ih x

private lemma row_isDist (hn : 1 ≤ n) (t : ℕ) (x : Fin n → ZMod 2) :
    IsDist (rowDist (hypercubeWalk n) t x) :=
  ⟨fun y => hc_pow_nonneg hn t x y, hc_pow_sum hn t x⟩

private lemma unif_isDist (n : ℕ) : IsDist (uniformDist (Fin n → ZMod 2)) := by
  have hN : (0 : ℝ) < (Fintype.card (Fin n → ZMod 2) : ℝ) := by
    have : 0 < Fintype.card (Fin n → ZMod 2) := Fintype.card_pos
    exact_mod_cast this
  refine ⟨fun x => by simp only [uniformDist]; positivity, ?_⟩
  simp only [uniformDist]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma unif_apply (n : ℕ) (y : Fin n → ZMod 2) :
    uniformDist (Fin n → ZMod 2) y = ((2 : ℝ) ^ n)⁻¹ := by
  simp only [uniformDist, card_hc]
  norm_num

private lemma tv_sq_bound (hn : 1 ≤ n) (t : ℕ) (x : Fin n → ZMod 2) :
    4 * (tvDist (rowDist (hypercubeWalk n) t x) (uniformDist (Fin n → ZMod 2))) ^ 2
      ≤ ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2), ((lamS n S) ^ t) ^ 2 := by
  have htv := (tv_eq_half_l1 (rowDist (hypercubeWalk n) t x) (uniformDist (Fin n → ZMod 2))
    (row_isDist hn t x) (unif_isDist n)).1
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n → ZMod 2)))
    (f := fun y => |((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹|)
  have hcard : ((Finset.univ : Finset (Fin n → ZMod 2)).card : ℝ) = (2 : ℝ) ^ n := by
    rw [Finset.card_univ, card_hc]
    norm_num
  have habs : ∀ y : Fin n → ZMod 2,
      |((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹| ^ 2
        = (((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹) ^ 2 := fun y => sq_abs _
  rw [hcard, Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => habs y),
    l2_identity hn t x] at hcs
  have hrw : (∑ y : Fin n → ZMod 2, |((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹|)
      = 2 * tvDist (rowDist (hypercubeWalk n) t x) (uniformDist (Fin n → ZMod 2)) := by
    rw [htv, Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => by
      rw [rowDist, unif_apply] :
      ∀ y ∈ Finset.univ, |rowDist (hypercubeWalk n) t x y - uniformDist (Fin n → ZMod 2) y|
        = |((hypercubeWalk n) ^ t) x y - ((2 : ℝ) ^ n)⁻¹|)]
    ring
  rw [hrw] at hcs
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hfin : (2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹ *
      ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2), ((lamS n S) ^ t) ^ 2)
      = ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2), ((lamS n S) ^ t) ^ 2 := by
    field_simp
  rw [hfin] at hcs
  nlinarith [hcs]

end TV

/-! ### Elementary bounds on total variation and `d(t)` -/

section Basic

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma tv_nonneg (μ ν : V → ℝ) : 0 ≤ tvDist μ ν := by
  have hb : BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    Set.Finite.bddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have h := le_ciSup hb (∅ : Finset V)
  simp only [Finset.sum_empty, sub_zero, abs_zero] at h
  exact h

private lemma tv_le_one (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) : tvDist μ ν ≤ 1 := by
  refine ciSup_le fun A => ?_
  have h1 : 0 ≤ ∑ x ∈ A, μ x := Finset.sum_nonneg fun x _ => hμ.1 x
  have h2 : ∑ x ∈ A, μ x ≤ 1 := by
    rw [← hμ.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun x _ _ => hμ.1 x
  have h3 : 0 ≤ ∑ x ∈ A, ν x := Finset.sum_nonneg fun x _ => hν.1 x
  have h4 : ∑ x ∈ A, ν x ≤ 1 := by
    rw [← hν.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun x _ _ => hν.1 x
  rw [abs_le]
  constructor <;> linarith

private lemma dS_nonneg [Nonempty V] (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) :
    0 ≤ distStationary P π t := by
  have hb : BddAbove (Set.range fun x : V => tvDist (rowDist P t x) π) :=
    Set.Finite.bddAbove (Set.range fun x : V => tvDist (rowDist P t x) π).toFinite
  exact le_trans (tv_nonneg (rowDist P t (Classical.arbitrary V)) π)
    (le_ciSup hb (Classical.arbitrary V))

end Basic

/-! ### The master upper bound -/

section Numeric

variable {n : ℕ}

private lemma wt_le (S : Fin n → ZMod 2) : wt S ≤ n := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => S i = 1)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this

private lemma lam_pow_le (hn : 1 ≤ n) (t : ℕ) (S : Fin n → ZMod 2) :
    ((lamS n S) ^ t) ^ 2 ≤ (Real.exp (-(2 * (t : ℝ) / n))) ^ (wt S) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : (wt S : ℝ) ≤ n := by exact_mod_cast wt_le S
  have h0 : 0 ≤ lamS n S := by
    rw [lamS, sub_nonneg, div_le_one hnR]
    exact hw
  have h1 : lamS n S ≤ Real.exp (-((wt S : ℝ) / n)) := by
    have h := Real.add_one_le_exp (-((wt S : ℝ) / n))
    rw [lamS]
    linarith
  calc ((lamS n S) ^ t) ^ 2 = (lamS n S) ^ (t * 2) := by rw [pow_mul]
    _ ≤ (Real.exp (-((wt S : ℝ) / n))) ^ (t * 2) := pow_le_pow_left₀ h0 h1 _
    _ = (Real.exp (-(2 * (t : ℝ) / n))) ^ (wt S) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
        try ring

private lemma sum_q_pow (q : ℝ) :
    ∑ S : Fin n → ZMod 2, q ^ (wt S) = (1 + q) ^ n := by
  classical
  have hterm : ∀ S : Fin n → ZMod 2, q ^ (wt S) = ∏ i : Fin n, (if S i = 1 then q else 1) := by
    intro S
    rw [wt, ← Finset.prod_const, Finset.prod_filter]
  rw [Finset.sum_congr rfl (fun S (_ : S ∈ Finset.univ) => hterm S),
    sum_prod_zmod2 (fun _ a => if a = 1 then q else 1)]
  have hfac : ∀ i : Fin n, (∑ a : ZMod 2, (if a = 1 then q else 1)) = 1 + q := by
    intro i
    rw [zmod2_univ, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1),
      if_neg (by decide : (0 : ZMod 2) ≠ 1), if_pos rfl]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hfac i), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private lemma sum_erase_bound (hn : 1 ≤ n) (t : ℕ) :
    ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2), ((lamS n S) ^ t) ^ 2
      ≤ (1 + Real.exp (-(2 * (t : ℝ) / n))) ^ n - 1 := by
  classical
  calc ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2), ((lamS n S) ^ t) ^ 2
      ≤ ∑ S ∈ Finset.univ.erase (0 : Fin n → ZMod 2),
          (Real.exp (-(2 * (t : ℝ) / n))) ^ (wt S) :=
        Finset.sum_le_sum fun S _ => lam_pow_le hn t S
    _ = (∑ S : Fin n → ZMod 2, (Real.exp (-(2 * (t : ℝ) / n))) ^ (wt S))
          - (Real.exp (-(2 * (t : ℝ) / n))) ^ (wt (0 : Fin n → ZMod 2)) := by
        rw [eq_sub_iff_add_eq]
        exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
    _ = (1 + Real.exp (-(2 * (t : ℝ) / n))) ^ n - 1 := by
        rw [sum_q_pow, wt_zero, pow_zero]

private lemma master (hn : 1 ≤ n) (t : ℕ) :
    distStationary (hypercubeWalk n) (uniformDist (Fin n → ZMod 2)) t
      ≤ 2⁻¹ * Real.sqrt ((1 + Real.exp (-(2 * (t : ℝ) / n))) ^ n - 1) := by
  refine ciSup_le fun x => ?_
  have h1 := tv_sq_bound hn t x
  have h2 := sum_erase_bound hn t
  have htv0 : 0 ≤ tvDist (rowDist (hypercubeWalk n) t x) (uniformDist (Fin n → ZMod 2)) :=
    tv_nonneg _ _
  have hsq : (2 * tvDist (rowDist (hypercubeWalk n) t x) (uniformDist (Fin n → ZMod 2))) ^ 2
      ≤ (1 + Real.exp (-(2 * (t : ℝ) / n))) ^ n - 1 := by nlinarith
  have hle := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by linarith)] at hle
  linarith

end Numeric

/-! ### The two ends of the cutoff window -/

section Limits

open Filter

private def Dn (n : ℕ) (α : ℝ) : ℝ :=
  distStationary (hypercubeWalk n) (uniformDist (Fin n → ZMod 2))
    ⌊2⁻¹ * (n : ℝ) * Real.log n + α * (n : ℝ)⌋₊

private lemma Dn_nonneg (n : ℕ) (α : ℝ) : 0 ≤ Dn n α := dS_nonneg _ _ _

private lemma Dn_le_one {n : ℕ} (hn : 1 ≤ n) (α : ℝ) : Dn n α ≤ 1 := by
  refine ciSup_le fun x => ?_
  exact tv_le_one _ _ (row_isDist hn _ x) (unif_isDist n)

private lemma Dn_lower (α : ℝ) (hα : α < 0) :
    ∀ᶠ n : ℕ in atTop, 1 - 8 * Real.exp (1 + 2 * α) ≤ Dn n α := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 2, hlog.eventually_ge_atTop (-2 * α)] with n hn hlg
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) ≤ 2⁻¹ * (n : ℝ) * Real.log n + α * (n : ℝ) := by nlinarith
  have ht : ((⌊2⁻¹ * (n : ℝ) * Real.log n + α * (n : ℝ)⌋₊ : ℕ) : ℝ)
      ≤ 2⁻¹ * (n : ℝ) * Real.log n - (-α) * (n : ℝ) := by
    have := Nat.floor_le hx
    linarith
  have h := hypercube_lower_bound n hn (-α) (by linarith)
    ⌊2⁻¹ * (n : ℝ) * Real.log n + α * (n : ℝ)⌋₊ ht
  rw [show (1 : ℝ) - 2 * -α = 1 + 2 * α from by ring] at h
  exact h

private lemma nq_bound {n : ℕ} (hn : 1 ≤ n) (α : ℝ) :
    (n : ℝ) * Real.exp (-(2 * ((⌊2⁻¹ * (n : ℝ) * Real.log n + α * (n : ℝ)⌋₊ : ℕ) : ℝ) / n))
      ≤ Real.exp (2 - 2 * α) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x : ℝ := 2⁻¹ * (n : ℝ) * Real.log n + α * (n : ℝ) with hxdef
  have hfl : x - 1 < ((⌊x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hd : (2 : ℝ) * (x - 1) / n ≤ 2 * ((⌊x⌋₊ : ℕ) : ℝ) / n := by
    gcongr
    try linarith
  have hval : (2 : ℝ) * (x - 1) / (n : ℝ) = Real.log n + 2 * α - 2 / n := by
    rw [hxdef]
    field_simp
    try ring
  have hexp : -(2 * ((⌊x⌋₊ : ℕ) : ℝ) / n) ≤ -Real.log n - 2 * α + 2 / n := by
    rw [hval] at hd
    linarith
  have hmono := Real.exp_le_exp.mpr hexp
  have hsplit : Real.exp (-Real.log (n : ℝ) - 2 * α + 2 / (n : ℝ))
      = (n : ℝ)⁻¹ * (Real.exp (-(2 * α)) * Real.exp (2 / (n : ℝ))) := by
    rw [show -Real.log (n : ℝ) - 2 * α + 2 / (n : ℝ)
        = (-Real.log (n : ℝ)) + (-(2 * α) + 2 / (n : ℝ)) from by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hn0]
  have h2n : Real.exp (2 / (n : ℝ)) ≤ Real.exp 2 := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_iff₀ hn0]
    nlinarith
  calc (n : ℝ) * Real.exp (-(2 * ((⌊x⌋₊ : ℕ) : ℝ) / n))
      ≤ (n : ℝ) * Real.exp (-Real.log (n : ℝ) - 2 * α + 2 / (n : ℝ)) := by nlinarith
    _ = Real.exp (-(2 * α)) * Real.exp (2 / (n : ℝ)) := by
        rw [hsplit]
        field_simp
    _ ≤ Real.exp (-(2 * α)) * Real.exp 2 := by
        have := Real.exp_pos (-(2 * α))
        nlinarith
    _ = Real.exp (2 - 2 * α) := by rw [← Real.exp_add]; congr 1; ring

private lemma Dn_upper (α : ℝ) :
    ∀ᶠ n : ℕ in atTop, Dn n α ≤ 2⁻¹ * Real.sqrt (Real.exp (Real.exp (2 - 2 * α)) - 1) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set t : ℕ := ⌊2⁻¹ * (n : ℝ) * Real.log n + α * (n : ℝ)⌋₊ with htdef
  set q : ℝ := Real.exp (-(2 * (t : ℝ) / n)) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hkey : (1 + q) ^ n ≤ Real.exp (Real.exp (2 - 2 * α)) := by
    calc (1 + q) ^ n ≤ (Real.exp q) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp q]) n
      _ = Real.exp ((n : ℝ) * q) := (Real.exp_nat_mul q n).symm
      _ ≤ Real.exp (Real.exp (2 - 2 * α)) := Real.exp_le_exp.mpr (nq_bound hn α)
  have hm := master hn t
  refine le_trans hm ?_
  have hsq : Real.sqrt ((1 + q) ^ n - 1) ≤ Real.sqrt (Real.exp (Real.exp (2 - 2 * α)) - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

end Limits

end

end MarkovMixing

open MarkovMixing Filter

/-- **Theorem 18.3** (LPW), the capstone of Chapter 18: the lazy random walk
on the `n`-dimensional hypercube has a cutoff at `(1/2) n log n` with a
window of size `n`. -/
theorem solution :
    HasCutoffWindow (fun n => hypercubeWalk n)
      (fun n => uniformDist (Fin n → ZMod 2))
      (fun n => 2⁻¹ * n * Real.log n) (fun n => n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the window is `o(t)`
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 2 / Real.log n) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hlog
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlp : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    field_simp
    try ring
  · -- far below the cutoff the distance is close to `1`
    have hexp : Tendsto (fun α : ℝ => Real.exp (1 + 2 * α)) atBot (nhds 0) := by
      have hl : Tendsto (fun α : ℝ => 1 + 2 * α) atBot atBot :=
        Filter.tendsto_atBot_add_const_left atBot 1
          (Filter.Tendsto.const_mul_atBot (by norm_num : (0:ℝ) < 2) tendsto_id)
      exact Real.tendsto_exp_atBot.comp hl
    have hg : Tendsto (fun α : ℝ => 1 - 8 * Real.exp (1 + 2 * α)) atBot (nhds 1) := by
      simpa using tendsto_const_nhds.sub (hexp.const_mul (8 : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun α : ℝ => 1 - 8 * Real.exp (1 + 2 * α)) (h := fun _ : ℝ => (1 : ℝ))
      hg tendsto_const_nhds ?_ ?_
    · filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with α hα
      show 1 - 8 * Real.exp (1 + 2 * α) ≤ liminf (fun n => Dn n α) atTop
      refine le_liminf_of_le ⟨1, fun a ha => ?_⟩ (Dn_lower α hα)
      rw [Filter.eventually_map] at ha
      obtain ⟨n, hn1, hn2⟩ := (ha.and (Filter.eventually_ge_atTop 1)).exists
      exact le_trans hn1 (Dn_le_one hn2 α)
    · filter_upwards with α
      show liminf (fun n => Dn n α) atTop ≤ 1
      refine liminf_le_of_le ⟨0, ?_⟩ ?_
      · rw [Filter.eventually_map]
        filter_upwards with n using Dn_nonneg n α
      · intro b hb
        obtain ⟨n, hn1, hn2⟩ := (hb.and (Filter.eventually_ge_atTop 1)).exists
        exact le_trans hn1 (Dn_le_one hn2 α)
  · -- far above the cutoff the distance is close to `0`
    have hlin : Tendsto (fun α : ℝ => 2 - 2 * α) atTop atBot := by
      have hneg : Tendsto (fun α : ℝ => -(2 * α)) atTop atBot :=
        Filter.tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id)
      have h := Filter.tendsto_atBot_add_const_left atTop 2 hneg
      refine Filter.Tendsto.congr ?_ h
      intro x
      ring
    have h2 : Tendsto (fun α : ℝ => Real.exp (2 - 2 * α)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hlin
    have h3 : Tendsto (fun α : ℝ => Real.exp (Real.exp (2 - 2 * α))) atTop (nhds 1) := by
      have h := (Real.continuous_exp.tendsto 0).comp h2
      simpa using h
    have h4 : Tendsto (fun α : ℝ => Real.exp (Real.exp (2 - 2 * α)) - 1) atTop (nhds 0) := by
      simpa using h3.sub (tendsto_const_nhds (x := (1 : ℝ)))
    have h5 : Tendsto (fun α : ℝ => Real.sqrt (Real.exp (Real.exp (2 - 2 * α)) - 1)) atTop
        (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp h4
      simpa using h
    have hh : Tendsto
        (fun α : ℝ => 2⁻¹ * Real.sqrt (Real.exp (Real.exp (2 - 2 * α)) - 1)) atTop (nhds 0) := by
      simpa using h5.const_mul (2⁻¹ : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℝ => (0 : ℝ))
      (h := fun α : ℝ => 2⁻¹ * Real.sqrt (Real.exp (Real.exp (2 - 2 * α)) - 1))
      tendsto_const_nhds hh ?_ ?_
    · filter_upwards with α
      show (0 : ℝ) ≤ limsup (fun n => Dn n α) atTop
      refine le_limsup_of_le ⟨1, ?_⟩ ?_
      · rw [Filter.eventually_map]
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn using Dn_le_one hn α
      · intro b hb
        obtain ⟨n, hn1⟩ := hb.exists
        exact le_trans (Dn_nonneg n α) hn1
    · filter_upwards with α
      show limsup (fun n => Dn n α) atTop
        ≤ 2⁻¹ * Real.sqrt (Real.exp (Real.exp (2 - 2 * α)) - 1)
      refine limsup_le_of_le ⟨0, fun a ha => ?_⟩ (Dn_upper α)
      rw [Filter.eventually_map] at ha
      obtain ⟨n, hn1⟩ := ha.exists
      exact le_trans (Dn_nonneg n α) hn1

-- Prove2me | solution 1 for LinearOptimization.integer_program_formulation_strength
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:04:30.2383+00:00
-- url     : https://prove2.me/submissions/2254524d-b39f-45ab-b17a-066e752cc79e

import Mathlib
import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_MstRelaxations

set_option autoImplicit false

namespace LinearOptimization

theorem mstSubtour_subset_cutset (n k : ℕ)
    (ends : Fin k → Fin n × Fin n) :
    mstSubtourRelaxation ends ⊆ mstCutsetRelaxation ends := by
  intro x hx
  rcases hx with ⟨htotal, hsub, hbox⟩
  refine ⟨htotal, ?_, hbox⟩
  intro S hSempty hSuniv
  have hComplEmpty : Sᶜ ≠ ∅ := by
    intro h
    exact hSuniv ((Finset.compl_eq_empty_iff S).mp h)
  have hComplUniv : Sᶜ ≠ Finset.univ := by
    intro h
    exact hSempty ((Finset.compl_eq_univ_iff S).mp h)
  have hleft := hsub S hSempty hSuniv
  have hright := hsub Sᶜ hComplEmpty hComplUniv
  have hcard : (S.card : ℝ) + ((Sᶜ).card : ℝ) = n := by
    have h := Finset.card_add_card_compl S
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  have hpartition :
      (∑ e ∈ Finset.univ.filter
        (fun e => (ends e).1 ∈ S ∧ (ends e).2 ∈ S), x e) +
      (∑ e ∈ Finset.univ.filter
        (fun e => (ends e).1 ∈ Sᶜ ∧ (ends e).2 ∈ Sᶜ), x e) +
      (∑ e ∈ Finset.univ.filter
        (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S) ∨
          ((ends e).1 ∉ S ∧ (ends e).2 ∈ S)), x e) =
      ∑ e, x e := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hfirst : (ends e).1 ∈ S <;>
      by_cases hsecond : (ends e).2 ∈ S <;>
      simp [hfirst, hsecond]
  linarith

end LinearOptimization

set_option autoImplicit false

open LinearOptimization

namespace MstWitness

def ends (e : Fin 9) : Fin 7 × Fin 7 :=
  match e.val with
  | 0 => (0, 1)
  | 1 => (1, 2)
  | 2 => (2, 0)
  | 3 => (0, 3)
  | 4 => (3, 4)
  | 5 => (4, 0)
  | 6 => (0, 5)
  | 7 => (5, 6)
  | _ => (6, 0)

def weightQ (e : Fin 9) : ℚ := if e.val < 3 then 1 else 1 / 2

def weight (e : Fin 9) : ℝ := (weightQ e : ℝ)

private def weightN (e : Fin 9) : ℕ := if e.val < 3 then 2 else 1

private def score (a b : Bool) (w : ℕ) : ℕ := if a = b then 0 else w

private theorem weightN_cast (e : Fin 9) : (weightN e : ℚ) = 2 * weightQ e := by
  dsimp [weightN, weightQ]
  split_ifs <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem boolean_cuts : ∀ a b c d e f g : Bool,
    (a || b || c || d || e || f || g) = true →
    (!a || !b || !c || !d || !e || !f || !g) = true →
    2 ≤ score a b 2 + score b c 2 + score c a 2 +
      score a d 1 + score d e 1 + score e a 1 +
      score a f 1 + score f g 1 + score g a 1 := by
  decide

private theorem integer_cuts (S : Finset (Fin 7))
    (hSempty : S ≠ ∅) (hSuniv : S ≠ Finset.univ) :
    2 ≤ ∑ e ∈ Finset.univ.filter
      (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S) ∨
        ((ends e).1 ∉ S ∧ (ends e).2 ∈ S)), weightN e := by
  let b : Fin 7 → Bool := fun i => decide (i ∈ S)
  have hin : (b 0 || b 1 || b 2 || b 3 || b 4 || b 5 || b 6) = true := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
    fin_cases i <;> simp [b] <;> tauto
  have hmissing : ∃ i : Fin 7, i ∉ S := by
    by_contra h
    push Not at h
    exact hSuniv (Finset.eq_univ_iff_forall.mpr h)
  have hout : (!b 0 || !b 1 || !b 2 || !b 3 || !b 4 || !b 5 || !b 6) = true := by
    obtain ⟨i, hi⟩ := hmissing
    fin_cases i <;> simp [b] <;> tauto
  have hscore :
      (∑ e, score (b (ends e).1) (b (ends e).2) (weightN e)) =
      ∑ e ∈ Finset.univ.filter
        (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S) ∨
          ((ends e).1 ∉ S ∧ (ends e).2 ∈ S)), weightN e := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hfirst : (ends e).1 ∈ S <;>
      by_cases hsecond : (ends e).2 ∈ S <;>
      simp [score, b, hfirst, hsecond]
  rw [← hscore]
  have h := boolean_cuts (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) hin hout
  simpa [ends, weightN, Fin.sum_univ_succ, Nat.add_assoc] using h

theorem rational_cuts (S : Finset (Fin 7))
    (hSempty : S ≠ ∅) (hSuniv : S ≠ Finset.univ) :
    1 ≤ ∑ e ∈ Finset.univ.filter
      (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S) ∨
        ((ends e).1 ∉ S ∧ (ends e).2 ∈ S)), weightQ e := by
  have h : (2 : ℚ) ≤ ∑ e ∈ Finset.univ.filter
      (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S) ∨
        ((ends e).1 ∉ S ∧ (ends e).2 ∈ S)), (weightN e : ℚ) := by
    exact_mod_cast integer_cuts S hSempty hSuniv
  simp_rw [weightN_cast] at h
  rw [← Finset.mul_sum] at h
  linarith

theorem feasible : weight ∈ mstCutsetRelaxation ends := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [weight, weightQ, Fin.sum_univ_succ]
  · intro S hS hS'
    simp only [weight]
    exact_mod_cast rational_cuts S hS hS'
  · intro e
    fin_cases e <;> norm_num [weight, weightQ]

theorem not_subtour : weight ∉ mstSubtourRelaxation ends := by
  intro h
  have hS := h.2.1 ({0, 1, 2} : Finset (Fin 7)) (by decide) (by decide)
  have hcard : ({0, 1, 2} : Finset (Fin 7)).card = 3 := by decide
  have hsumN : (∑ e ∈ Finset.univ.filter
      (fun e => (ends e).1 ∈ ({0, 1, 2} : Finset (Fin 7)) ∧
        (ends e).2 ∈ ({0, 1, 2} : Finset (Fin 7))), weightN e) = 6 := by
    decide
  have hsumQ : (∑ e ∈ Finset.univ.filter
      (fun e => (ends e).1 ∈ ({0, 1, 2} : Finset (Fin 7)) ∧
        (ends e).2 ∈ ({0, 1, 2} : Finset (Fin 7))), weightQ e) = 3 := by
    have hcast : (∑ e ∈ Finset.univ.filter
        (fun e => (ends e).1 ∈ ({0, 1, 2} : Finset (Fin 7)) ∧
          (ends e).2 ∈ ({0, 1, 2} : Finset (Fin 7))), (weightN e : ℚ)) = 6 := by
      exact_mod_cast hsumN
    simp_rw [weightN_cast] at hcast
    rw [← Finset.mul_sum] at hcast
    linarith
  have hsum : (∑ e ∈ Finset.univ.filter
      (fun e => (ends e).1 ∈ ({0, 1, 2} : Finset (Fin 7)) ∧
        (ends e).2 ∈ ({0, 1, 2} : Finset (Fin 7))), weight e) = 3 := by
    simp only [weight]
    exact_mod_cast hsumQ
  rw [hsum, hcard] at hS
  norm_num at hS

theorem fractional : ¬∃ z : ℤ, weight 3 = (z : ℝ) := by
  rintro ⟨z, hz⟩
  norm_num [weight, weightQ] at hz
  have hlo : (0 : ℝ) < z := by linarith
  have hhi : (z : ℝ) < 1 := by linarith
  have hzlo : 0 < z := by exact_mod_cast hlo
  have hzhi : z < 1 := by exact_mod_cast hhi
  omega

theorem noLoops (e : Fin 9) : (ends e).1 ≠ (ends e).2 := by
  fin_cases e <;> norm_num [ends, Fin.ext_iff]

end MstWitness

set_option autoImplicit false

namespace MstExtreme

theorem lower_eq {a b Y Z C : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hY : C ≤ Y) (hZ : C ≤ Z)
    (hmix : a * Y + b * Z = C) : Y = C := by
  have hc : a * C + b * C = C := by rw [← add_mul, hab, one_mul]
  have hp : 0 ≤ b * (Z - C) := mul_nonneg hb.le (sub_nonneg.mpr hZ)
  have hle : a * Y ≤ a * C := by nlinarith only [hmix, hc, hp]
  exact le_antisymm ((mul_le_mul_iff_right₀ ha).mp hle) hY

theorem upper_eq {a b Y Z C : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hY : Y ≤ C) (hZ : Z ≤ C)
    (hmix : a * Y + b * Z = C) : Y = C := by
  have h := lower_eq ha hb hab (neg_le_neg hY) (neg_le_neg hZ)
    (show a * (-Y) + b * (-Z) = -C by nlinarith only [hmix])
  exact neg_injective h

theorem extreme_of_constraints (A : Set (Fin 9 → ℝ)) (w : Fin 9 → ℝ)
    (hw : w ∈ A)
    (hwval : ∀ i, w i = if i.val < 3 then 1 else 1 / 2)
    (hbox : ∀ x ∈ A, ∀ i, x i ≤ 1)
    (hcuts : ∀ x ∈ A,
      1 ≤ x 3 + x 4 ∧ 1 ≤ x 4 + x 5 ∧ 1 ≤ x 3 + x 5 ∧
      1 ≤ x 6 + x 7 ∧ 1 ≤ x 7 + x 8 ∧ 1 ≤ x 6 + x 8) :
    w ∈ Set.extremePoints ℝ A := by
  refine ⟨hw, ?_⟩
  intro y hy z hz hseg
  rcases hseg with ⟨a, b, ha, hb, hab, hmix⟩
  have he (i : Fin 9) : a * y i + b * z i = w i := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hmix i
  have hunit (i : Fin 9) (hi : i.val < 3) : y i = 1 := by
    apply upper_eq ha hb hab (hbox y hy i) (hbox z hz i)
    simpa [hwval, hi] using he i
  have hpair (i j : Fin 9) (hi : 3 ≤ i.val) (hj : 3 ≤ j.val)
      (hY : 1 ≤ y i + y j) (hZ : 1 ≤ z i + z j) : y i + y j = 1 := by
    apply lower_eq ha hb hab hY hZ
    have hei := he i
    have hej := he j
    simp only [hwval, if_neg (not_lt.mpr hi)] at hei
    simp only [hwval, if_neg (not_lt.mpr hj)] at hej
    nlinarith only [hei, hej]
  rcases hcuts y hy with ⟨hy34, hy45, hy35, hy67, hy78, hy68⟩
  rcases hcuts z hz with ⟨hz34, hz45, hz35, hz67, hz78, hz68⟩
  have h34 := hpair 3 4 (by decide) (by decide) hy34 hz34
  have h45 := hpair 4 5 (by decide) (by decide) hy45 hz45
  have h35 := hpair 3 5 (by decide) (by decide) hy35 hz35
  have h67 := hpair 6 7 (by decide) (by decide) hy67 hz67
  have h78 := hpair 7 8 (by decide) (by decide) hy78 hz78
  have h68 := hpair 6 8 (by decide) (by decide) hy68 hz68
  funext i
  rw [hwval]
  fin_cases i
  · exact hunit 0 (by decide)
  · exact hunit 1 (by decide)
  · exact hunit 2 (by decide)
  · change y 3 = 1 / 2
    linarith only [h34, h45, h35]
  · change y 4 = 1 / 2
    linarith only [h34, h45, h35]
  · change y 5 = 1 / 2
    linarith only [h34, h45, h35]
  · change y 6 = 1 / 2
    linarith only [h67, h78, h68]
  · change y 7 = 1 / 2
    linarith only [h67, h78, h68]
  · change y 8 = 1 / 2
    linarith only [h67, h78, h68]

end MstExtreme

namespace MstWitness

private theorem cut_two (x : Fin 9 → ℝ) (hx : x ∈ mstCutsetRelaxation ends)
    (S : Finset (Fin 7)) (i j : Fin 9) (hS : S ≠ ∅) (hS' : S ≠ Finset.univ)
    (hcut : Finset.univ.filter
      (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S) ∨
        ((ends e).1 ∉ S ∧ (ends e).2 ∈ S)) = {i, j})
    (hij : i ≠ j) : 1 ≤ x i + x j := by
  have h := hx.2.1 S hS hS'
  rw [hcut, Finset.sum_pair hij] at h
  exact h

theorem six_cuts (x : Fin 9 → ℝ) (hx : x ∈ mstCutsetRelaxation ends) :
    1 ≤ x 3 + x 4 ∧ 1 ≤ x 4 + x 5 ∧ 1 ≤ x 3 + x 5 ∧
    1 ≤ x 6 + x 7 ∧ 1 ≤ x 7 + x 8 ∧ 1 ≤ x 6 + x 8 := by
  exact ⟨cut_two x hx {3} 3 4 (by decide) (by decide) (by decide) (by decide),
    cut_two x hx {4} 4 5 (by decide) (by decide) (by decide) (by decide),
    cut_two x hx {3, 4} 3 5 (by decide) (by decide) (by decide) (by decide),
    cut_two x hx {5} 6 7 (by decide) (by decide) (by decide) (by decide),
    cut_two x hx {6} 7 8 (by decide) (by decide) (by decide) (by decide),
    cut_two x hx {5, 6} 6 8 (by decide) (by decide) (by decide) (by decide)⟩

theorem extreme : weight ∈ Set.extremePoints ℝ (mstCutsetRelaxation ends) := by
  apply MstExtreme.extreme_of_constraints _ _ feasible
  · intro i
    dsimp [weight, weightQ]
    split_ifs <;> norm_num
  · intro x hx i
    exact (hx.2.2 i).2
  · exact six_cuts

end MstWitness

theorem solution :
    (∀ (n k : ℕ) (ends : Fin k → Fin n × Fin n),
      mstSubtourRelaxation ends ⊆ mstCutsetRelaxation ends) ∧
    (∃ (n k : ℕ) (ends : Fin k → Fin n × Fin n),
      ¬mstCutsetRelaxation ends ⊆ mstSubtourRelaxation ends) ∧
    (∃ (n k : ℕ) (ends : Fin k → Fin n × Fin n) (x : Fin k → ℝ),
      x ∈ Set.extremePoints ℝ (mstCutsetRelaxation ends) ∧
      ∃ e, ¬∃ z : ℤ, x e = (z : ℝ)) := by
  refine ⟨LinearOptimization.mstSubtour_subset_cutset, ?_, ?_⟩
  · refine ⟨7, 9, MstWitness.ends, ?_⟩
    intro h
    exact MstWitness.not_subtour (h MstWitness.feasible)
  · exact ⟨7, 9, MstWitness.ends, MstWitness.weight,
      MstWitness.extreme, 3, MstWitness.fractional⟩

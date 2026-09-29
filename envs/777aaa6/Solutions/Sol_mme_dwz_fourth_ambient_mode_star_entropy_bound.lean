-- Prove2me | solution 1 for mme_dwz_fourth_ambient_mode_star_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T20:51:39.768298+00:00
-- url     : https://prove2.me/submissions/80225175-d01b-400d-b3a9-dc4571a4b87c

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Card
import Theorems.Thm_mme_regional_dependent_profile_entropy_bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset


open BigOperators
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZAmbientStarCount

variable {Cell Mode Grade : Type*}
variable [Fintype Cell] [DecidableEq Cell]
variable [Fintype Mode] [DecidableEq Mode]
variable [Fintype Grade] [DecidableEq Grade]

noncomputable def histogram {N : ℕ} (w : Fin N → Cell) : Cell → Fin (N + 1) :=
  fun c ↦ ⟨Fintype.card {t : Fin N // w t = c}, by
    apply Nat.lt_succ_of_le
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_le (fun t : Fin N ↦ w t = c)⟩

def Admissible {N : ℕ} (grade : Cell → Mode → Grade)
    (M : Mode → Grade → ℕ) (h : Cell → Fin (N + 1)) : Prop :=
  ∀ i g, (∑ c : {c : Cell // grade c i = g}, (h c.val).val) = M i g

noncomputable def tables (N : ℕ) (grade : Cell → Mode → Grade)
    (M : Mode → Grade → ℕ) : Finset (Cell → Fin (N + 1)) :=
  Finset.univ.filter (Admissible grade M)

abbrev StarWords {N : ℕ} (grade : Cell → Mode → Grade)
    (M : Mode → Grade → ℕ) (mode : Mode) (x : Fin N → Grade) :=
  {w : Fin N → Cell // (∀ t, grade (w t) mode = x t) ∧
    ∀ i g, Fintype.card {t : Fin N // grade (w t) i = g} = M i g}

omit [Fintype Grade] in
theorem sum_histogram {N : ℕ} (w : Fin N → Cell)
    (coarse : Cell → Grade) (g : Grade) :
    (∑ c : {c : Cell // coarse c = g}, (histogram w c.val).val) =
      Fintype.card {t : Fin N // coarse (w t) = g} := by
  let e := Equiv.sigmaSubtypeFiberEquivSubtype w
    (p := fun t ↦ coarse (w t) = g) (q := fun c ↦ coarse c = g)
    (fun _ ↦ Iff.rfl)
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_sigma, histogram] using hc

omit [Fintype Cell] in
theorem histogram_eq_iff {N : ℕ} (w : Fin N → Cell)
    (h : Cell → Fin (N + 1)) :
    histogram w = h ↔ ∀ c, Fintype.card {t : Fin N // w t = c} = (h c).val := by
  constructor
  · intro he c
    exact congrArg Fin.val (congrFun he c)
  · intro he
    funext c
    exact Fin.ext (he c)

omit [DecidableEq Mode] in
theorem word_star_card (N : ℕ) (grade : Cell → Mode → Grade)
    (M : Mode → Grade → ℕ) (mode : Mode) (x : Fin N → Grade)
    (hx : ∀ g, Fintype.card {t : Fin N // x t = g} = M mode g) :
    Nat.card (StarWords grade M mode x) =
      ∑ h ∈ tables N grade M,
        ∏ g, (M mode g).factorial /
          ∏ c : {c : Cell // grade c mode = g}, ((h c.val).val).factorial := by
  classical
  let star : Finset (Fin N → Cell) := Finset.univ.filter (fun w ↦
    (∀ t, grade (w t) mode = x t) ∧
      ∀ i g, Fintype.card {t : Fin N // grade (w t) i = g} = M i g)
  have hmap : (star : Set (Fin N → Cell)).MapsTo histogram (tables N grade M) := by
    intro w hw
    obtain ⟨_, hm⟩ := (Finset.mem_filter.mp hw).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i g
    exact (sum_histogram w (fun c ↦ grade c i) g).trans (hm i g)
  have hpartition := Finset.card_eq_sum_card_fiberwise hmap
  have hfiber (h : Cell → Fin (N + 1)) (hh : h ∈ tables N grade M) :
      (star.filter (fun w ↦ histogram w = h)).card =
        ∏ g, (M mode g).factorial /
          ∏ c : {c : Cell // grade c mode = g}, ((h c.val).val).factorial := by
    have hadm : Admissible grade M h := (Finset.mem_filter.mp hh).2
    have hpred (w : Fin N → Cell) :
        (((∀ t, grade (w t) mode = x t) ∧
          ∀ i g, Fintype.card {t : Fin N // grade (w t) i = g} = M i g) ∧
          histogram w = h) ↔
        ((∀ t, grade (w t) mode = x t) ∧
          ∀ c, Fintype.card {t : Fin N // w t = c} = (h c).val) := by
      constructor
      · rintro ⟨⟨hw, _⟩, he⟩
        exact ⟨hw, (histogram_eq_iff w h).mp he⟩
      · rintro ⟨hw, hc⟩
        have he := (histogram_eq_iff w h).mpr hc
        refine ⟨⟨hw, ?_⟩, he⟩
        intro i g
        rw [← sum_histogram w (fun c ↦ grade c i) g, he]
        exact hadm i g
    have hcount := mme_fintype_constrained_prescribed_fiber_function_card
      x (fun c ↦ grade c mode) (fun c ↦ (h c).val)
      (fun g ↦ (hadm mode g).trans (hx g).symm)
    have heq : (star.filter (fun w ↦ histogram w = h)).card =
        Nat.card {w : Fin N → Cell //
          (∀ t, grade (w t) mode = x t) ∧
          ∀ c, Fintype.card {t : Fin N // w t = c} = (h c).val} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply congrArg Finset.card
      ext w
      simp only [star, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpred w
    rw [heq, hcount]
    simp only [hx]
  have hcard : Nat.card (StarWords grade M mode x) = star.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard, hpartition]
  exact Finset.sum_congr rfl hfiber

abbrev FourthCell := {sigma : Fin 3 → Fin 9 // (∑ i, (sigma i).val) = 8}

noncomputable def addressStarEquiv (N : ℕ) (M : Fin 3 → Fin 9 → ℕ)
    (mode : Fin 3) (x : Fin N → Fin 9) :
    {a : Fin 3 → Fin N → Fin 9 //
      (∀ t, (∑ i, (a i t).val) = 8) ∧
      (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧ a mode = x} ≃
      StarWords (fun c : FourthCell ↦ c.val) M mode x where
  toFun a := ⟨fun t ↦ ⟨fun i ↦ a.val i t, a.property.1 t⟩,
    ⟨fun t ↦ congrFun a.property.2.2 t, a.property.2.1⟩⟩
  invFun w := ⟨fun i t ↦ (w.val t).val i,
    ⟨fun t ↦ (w.val t).property, w.property.2, funext w.property.1⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem ambient_mode_star_card (N : ℕ) (M : Fin 3 → Fin 9 → ℕ)
    (mode : Fin 3) (x : Fin N → Fin 9)
    (hx : ∀ g, Fintype.card {t : Fin N // x t = g} = M mode g) :
    let Cell := {sigma : Fin 3 → Fin 9 // (∑ i, (sigma i).val) = 8}
    let admissible : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ sigma : {sigma : Cell // sigma.val i = g}, (h sigma.val).val) = M i g)
    Nat.card {a : Fin 3 → Fin N → Fin 9 //
      (∀ t, (∑ i, (a i t).val) = 8) ∧
      (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧ a mode = x} =
      ∑ h ∈ admissible, ∏ g : Fin 9,
        (M mode g).factorial /
          ∏ sigma : {sigma : Cell // sigma.val mode = g},
            ((h sigma.val).val).factorial := by
  refine (Nat.card_congr (addressStarEquiv N M mode x)).trans ?_
  refine (word_star_card N (fun c : FourthCell ↦ c.val) M mode x hx).trans ?_
  apply Finset.sum_congr
  · ext h
    simp only [tables, Finset.mem_filter, Finset.mem_univ, true_and, Admissible]
  · intro h _
    rfl

end MME.DWZAmbientStarCount



open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem fourth_support_card :
    Fintype.card {sigma : Fin 3 → Fin 9 // (∑ i, (sigma i).val) = 8} = 45 := by
  decide



open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZAmbientEntropy

theorem massEntropy_nat {C : Type*} [Fintype C] (n : C → ℕ) :
    massEntropy (fun c ↦ (n c : ℝ)) =
      ((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ) := by
  simp only [massEntropy, entropy, Real.negMulLog, neg_mul,
    Finset.sum_neg_distrib, Nat.cast_sum]
  ring

theorem massEntropy_mul {C : Type*} [Fintype C] (x : C → ℝ) (m : ℝ) :
    massEntropy (fun c ↦ x c * m) = m * massEntropy x := by
  unfold massEntropy entropy
  rw [← Finset.sum_mul, Real.negMulLog_mul]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem fiber_massEntropy {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (n : C → ℕ) (M : G → ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, n c.val = M g) :
    (∑ g, massEntropy (fun c : {c : C // grade c = g} ↦ (n c.val : ℝ))) =
      (∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ) := by
  classical
  simp_rw [massEntropy_nat, hrow]
  rw [Finset.sum_sub_distrib,
    Fintype.sum_fiberwise grade (fun c ↦ (n c : ℝ) * Real.log (n c : ℝ))]

theorem fiber_factorial_entropy_bounds {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (n : C → ℕ) (M : G → ℕ) (S : ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, n c.val = M g)
    (hS : ∀ g, M g ≤ S) :
    ((∏ g, (M g).factorial /
      ∏ c : {c : C // grade c = g}, (n c.val).factorial : ℕ) : ℝ) ≤
        Real.exp ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
          ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ∧
    Real.exp ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
          ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ≤
      (6 * ((S : ℝ) + 1)) ^ Fintype.card C *
        ((∏ g, (M g).factorial /
          ∏ c : {c : C // grade c = g}, (n c.val).factorial : ℕ) : ℝ) := by
  classical
  have hc : (∑ g, Fintype.card {c : C // grade c = g}) = Fintype.card C := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      (Fintype.sum_fiberwise grade (fun _ ↦ (1 : ℕ)))
  have h := mme_regional_dependent_profile_entropy_bounds
    (fun g (c : {c : C // grade c = g}) ↦ n c.val) S
    (fun g ↦ (hrow g).trans_le (hS g))
  simpa only [fiber_massEntropy grade n M hrow, hc, hrow, Nat.cast_prod] using h

theorem multinomial_entropy_bounds {C : Type*} [Fintype C] (n : C → ℕ) :
    (Nat.multinomial Finset.univ n : ℝ) ≤
      Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ∧
    Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ≤
      (6 * (((∑ c, n c : ℕ) : ℝ) + 1)) ^ Fintype.card C *
        (Nat.multinomial Finset.univ n : ℝ) := by
  classical
  have h := mme_regional_dependent_profile_entropy_bounds
    (R := Unit) (fun _ ↦ n) (∑ c, n c) (fun _ ↦ le_refl _)
  simpa only [Fintype.prod_unique, Fintype.sum_unique, massEntropy_nat,
    Nat.multinomial] using h

theorem multinomial_cast_eq_real_factorial_quotient {C : Type*} [Fintype C]
    (n : C → ℕ) :
    (Nat.multinomial Finset.univ n : ℝ) =
      (((∑ c, n c).factorial : ℕ) : ℝ) / ∏ c, ((n c).factorial : ℝ) := by
  classical
  rw [Nat.multinomial, Nat.cast_div_charZero
    (Nat.prod_factorial_dvd_factorial_sum Finset.univ n), Nat.cast_prod]

theorem real_factorial_quotient_entropy_bounds {C : Type*} [Fintype C]
    (n : C → ℕ) :
    ((((∑ c, n c).factorial : ℕ) : ℝ) / ∏ c, ((n c).factorial : ℝ)) ≤
      Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ∧
    Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ≤
      (6 * (((∑ c, n c : ℕ) : ℝ) + 1)) ^ Fintype.card C *
        ((((∑ c, n c).factorial : ℕ) : ℝ) / ∏ c, ((n c).factorial : ℝ)) := by
  simpa only [multinomial_cast_eq_real_factorial_quotient] using
    multinomial_entropy_bounds n

theorem scaled_multinomial_log_bounds {C : Type*} [Fintype C]
    (a : C → ℕ) (m : ℕ) :
    (m : ℝ) * massEntropy (fun c ↦ (a c : ℝ)) -
        (Fintype.card C : ℝ) *
          Real.log (6 * ((((∑ c, a c) * m : ℕ) : ℝ) + 1)) ≤
      Real.log (Nat.multinomial Finset.univ (fun c ↦ a c * m) : ℝ) ∧
    Real.log (Nat.multinomial Finset.univ (fun c ↦ a c * m) : ℝ) ≤
      (m : ℝ) * massEntropy (fun c ↦ (a c : ℝ)) := by
  classical
  have h := multinomial_entropy_bounds (fun c ↦ a c * m)
  simp only [← massEntropy_nat] at h
  simp only [Nat.cast_mul, Nat.cast_sum, massEntropy_mul, ← Finset.sum_mul] at h
  have hpos : (0 : ℝ) < Nat.multinomial Finset.univ (fun c ↦ a c * m) := by
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ) (f := fun c ↦ a c * m)
  have hbase : (0 : ℝ) < 6 * (((∑ c, (a c : ℝ)) * (m : ℝ)) + 1) := by positivity
  have hup := Real.log_le_log hpos h.1
  rw [Real.log_exp] at hup
  have hlo := Real.log_le_log (Real.exp_pos _) h.2
  rw [Real.log_exp, Real.log_mul (pow_pos hbase _).ne' hpos.ne', Real.log_pow] at hlo
  constructor
  · simp only [Nat.cast_mul, Nat.cast_sum]
    linarith
  · exact hup

end MME.DWZAmbientEntropy



open BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZAmbientIndexedAdapter

/-- Every indexed ambient competitor injects into the full marginal-supported
star. Marginals are required for ALL ambient members, not only targets. -/
theorem indexed_star_card_le
    {N : ℕ} {ι : Type*} [DecidableEq ι]
    (address : ι → Fin 3 → Fin N → Fin 9)
    (M : Fin 3 → Fin 9 → ℕ) (ambient : Finset ι)
    (hsupport : ∀ j ∈ ambient, ∀ t, ∑ i, (address j i t).val = 8)
    (hmarginal : ∀ j ∈ ambient, ∀ i g,
      Fintype.card {t : Fin N // address j i t = g} = M i g)
    (hinj : Set.InjOn address (ambient : Set ι))
    (mode : Fin 3) (x : Fin N → Fin 9) :
    (ambient.filter (fun j ↦ address j mode = x)).card ≤
      Nat.card {a : Fin 3 → Fin N → Fin 9 //
        (∀ t, ∑ i, (a i t).val = 8) ∧
        (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧
        a mode = x} := by
  classical
  let source := ambient.filter (fun j ↦ address j mode = x)
  let target := {a : Fin 3 → Fin N → Fin 9 //
    (∀ t, ∑ i, (a i t).val = 8) ∧
    (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧ a mode = x}
  let f : source → target := fun j ↦
    ⟨address j.val, hsupport j.val (Finset.mem_filter.mp j.property).1,
      hmarginal j.val (Finset.mem_filter.mp j.property).1,
      (Finset.mem_filter.mp j.property).2⟩
  have hf : Function.Injective f := by
    intro j l h
    apply Subtype.ext
    exact hinj (Finset.mem_filter.mp j.property).1
      (Finset.mem_filter.mp l.property).1 (congrArg Subtype.val h)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_le_card_of_injective f hf

/-- If the indexed ambient family also contains every marginal-supported
address, its star count equals the full canonical count. -/
theorem indexed_star_card_eq
    {N : ℕ} {ι : Type*} [DecidableEq ι]
    (address : ι → Fin 3 → Fin N → Fin 9)
    (M : Fin 3 → Fin 9 → ℕ) (ambient : Finset ι)
    (hsupport : ∀ j ∈ ambient, ∀ t, ∑ i, (address j i t).val = 8)
    (hmarginal : ∀ j ∈ ambient, ∀ i g,
      Fintype.card {t : Fin N // address j i t = g} = M i g)
    (hinj : Set.InjOn address (ambient : Set ι))
    (hcomplete : ∀ a : Fin 3 → Fin N → Fin 9,
      (∀ t, ∑ i, (a i t).val = 8) →
      (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) →
      ∃ j ∈ ambient, address j = a)
    (mode : Fin 3) (x : Fin N → Fin 9) :
    (ambient.filter (fun j ↦ address j mode = x)).card =
      Nat.card {a : Fin 3 → Fin N → Fin 9 //
        (∀ t, ∑ i, (a i t).val = 8) ∧
        (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧
        a mode = x} := by
  classical
  let source := ambient.filter (fun j ↦ address j mode = x)
  let target := {a : Fin 3 → Fin N → Fin 9 //
    (∀ t, ∑ i, (a i t).val = 8) ∧
    (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧ a mode = x}
  let f : source → target := fun j ↦
    ⟨address j.val, hsupport j.val (Finset.mem_filter.mp j.property).1,
      hmarginal j.val (Finset.mem_filter.mp j.property).1,
      (Finset.mem_filter.mp j.property).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j l h
      apply Subtype.ext
      exact hinj (Finset.mem_filter.mp j.property).1
        (Finset.mem_filter.mp l.property).1 (congrArg Subtype.val h)
    · intro a
      obtain ⟨j, hj, hja⟩ := hcomplete a.val a.property.1 a.property.2.1
      refine ⟨⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩, ?_⟩
      · exact (congrFun hja mode).trans a.property.2.2
      · exact Subtype.ext hja
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_congr (Equiv.ofBijective f hf)

end MME.DWZAmbientIndexedAdapter



open BigOperators
open scoped Classical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZAmbientStarEntropy

open MME.DWZAmbientStarCount MME.DWZAmbientEntropy

/-- The polynomial number of possible joint histograms. No feasibility or
positivity assumption is needed: every entry is an integer between zero and N. -/
theorem admissible_card_le (N : ℕ) (M : Fin 3 → Fin 9 → ℕ) :
    (tables N (fun c : FourthCell ↦ c.val) M).card ≤ (N + 1) ^ 45 := by
  classical
  have h := (tables N (fun c : FourthCell ↦ c.val) M).card_le_univ
  simpa only [Fintype.card_fun, Fintype.card_fin, FourthCell, fourth_support_card] using h

/-- An entropy ceiling over ALL joint histograms gives an ambient star bound,
including competitors whose joint distribution differs from the target's. -/
theorem ambient_mode_star_entropy_bound
    (N : ℕ) (M : Fin 3 → Fin 9 → ℕ) (mode : Fin 3) (x : Fin N → Fin 9)
    (hx : ∀ g, Fintype.card {t : Fin N // x t = g} = M mode g)
    (E : ℝ)
    (hE : ∀ h ∈ tables N (fun c : FourthCell ↦ c.val) M,
      (∑ g, (M mode g : ℝ) * Real.log (M mode g : ℝ)) -
        ∑ c : FourthCell, ((h c).val : ℝ) * Real.log ((h c).val : ℝ) ≤ E) :
    (Nat.card {a : Fin 3 → Fin N → Fin 9 //
      (∀ t, ∑ i, (a i t).val = 8) ∧
      (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧
      a mode = x} : ℝ) ≤
        ((N : ℝ) + 1) ^ 45 * Real.exp E := by
  classical
  let T := tables N (fun c : FourthCell ↦ c.val) M
  have hM (g : Fin 9) : M mode g ≤ N := by
    rw [← hx g]
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_le (fun t : Fin N ↦ x t = g))
  have hweight (h : FourthCell → Fin (N + 1)) (hh : h ∈ T) :
      ((∏ g : Fin 9, (M mode g).factorial /
        ∏ c : {c : FourthCell // c.val mode = g}, ((h c.val).val).factorial : ℕ) : ℝ)
        ≤ Real.exp E := by
    have hadm : Admissible (fun c : FourthCell ↦ c.val) M h :=
      (Finset.mem_filter.mp hh).2
    have hrow : ∀ g : Fin 9,
        (∑ c : {c : FourthCell // c.val mode = g}, (h c.val).val) = M mode g := by
      intro g
      convert hadm mode g using 1
    have hb := (fiber_factorial_entropy_bounds (C := FourthCell) (G := Fin 9)
      (fun c ↦ c.val mode)
      (fun c ↦ (h c).val) (M mode) N (by
        intro g
        convert hrow g using 1
        apply Finset.sum_congr
        · ext c
          simp only [Finset.mem_univ]
        · intro c _
          rfl) hM).1.trans
        (Real.exp_le_exp.mpr (hE h hh))
    convert hb using 1
    congr 1
    apply Finset.prod_congr rfl
    intro g _
    congr 1
    apply Finset.prod_congr
    · ext c
      simp only [Finset.mem_univ]
    · intro c _
      rfl
  have hcount : Nat.card {a : Fin 3 → Fin N → Fin 9 //
      (∀ t, ∑ i, (a i t).val = 8) ∧
      (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧ a mode = x} =
      ∑ h ∈ T, ∏ g : Fin 9, (M mode g).factorial /
        ∏ c : {c : FourthCell // c.val mode = g}, ((h c.val).val).factorial := by
    exact (Nat.card_congr (addressStarEquiv N M mode x)).trans
      (word_star_card N (fun c : FourthCell ↦ c.val) M mode x hx)
  rw [hcount, Nat.cast_sum]
  calc
    _ ≤ ∑ _h ∈ T, Real.exp E := Finset.sum_le_sum hweight
    _ = (T.card : ℝ) * Real.exp E := by simp
    _ ≤ ((N : ℝ) + 1) ^ 45 * Real.exp E := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos E).le
      exact_mod_cast admissible_card_le N M

/-- The same bound applies to any injectively indexed ambient family with
the specified support and marginals. Completeness is not required for a bound. -/
theorem indexed_ambient_mode_star_entropy_bound
    {N : ℕ} {ι : Type*} [DecidableEq ι]
    (address : ι → Fin 3 → Fin N → Fin 9)
    (M : Fin 3 → Fin 9 → ℕ) (ambient : Finset ι)
    (hsupport : ∀ j ∈ ambient, ∀ t, ∑ i, (address j i t).val = 8)
    (hmarginal : ∀ j ∈ ambient, ∀ i g,
      Fintype.card {t : Fin N // address j i t = g} = M i g)
    (hinj : Set.InjOn address (ambient : Set ι))
    (mode : Fin 3) (x : Fin N → Fin 9)
    (hx : ∀ g, Fintype.card {t : Fin N // x t = g} = M mode g)
    (E : ℝ)
    (hE : ∀ h ∈ tables N (fun c : FourthCell ↦ c.val) M,
      (∑ g, (M mode g : ℝ) * Real.log (M mode g : ℝ)) -
        ∑ c : FourthCell, ((h c).val : ℝ) * Real.log ((h c).val : ℝ) ≤ E) :
    ((ambient.filter (fun j ↦ address j mode = x)).card : ℝ) ≤
      ((N : ℝ) + 1) ^ 45 * Real.exp E := by
  have h := MME.DWZAmbientIndexedAdapter.indexed_star_card_le
    address M ambient hsupport hmarginal hinj mode x
  exact (Nat.cast_le.mpr h).trans (ambient_mode_star_entropy_bound N M mode x hx E hE)

end MME.DWZAmbientStarEntropy



open BigOperators
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution
    {N : ℕ} {ι : Type*} [DecidableEq ι]
    (address : ι → Fin 3 → Fin N → Fin 9)
    (M : Fin 3 → Fin 9 → ℕ) (ambient : Finset ι)
    (hsupport : ∀ j ∈ ambient, ∀ t, ∑ i, (address j i t).val = 8)
    (hmarginal : ∀ j ∈ ambient, ∀ i g,
      Fintype.card {t : Fin N // address j i t = g} = M i g)
    (hinj : Set.InjOn address (ambient : Set ι))
    (mode : Fin 3) (x : Fin N → Fin 9)
    (hx : ∀ g, Fintype.card {t : Fin N // x t = g} = M mode g)
    (E : ℝ) :
    let Cell := {sigma : Fin 3 → Fin 9 // (∑ i, (sigma i).val) = 8}
    let admissible : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ c : {c : Cell // c.val i = g}, (h c.val).val) = M i g)
    (∀ h ∈ admissible,
      (∑ g, (M mode g : ℝ) * Real.log (M mode g : ℝ)) -
        ∑ c : Cell, ((h c).val : ℝ) * Real.log ((h c).val : ℝ) ≤ E) →
    ((ambient.filter (fun j ↦ address j mode = x)).card : ℝ) ≤
      ((N : ℝ) + 1) ^ 45 * Real.exp E := by
  intro Cell admissible hE
  apply MME.DWZAmbientStarEntropy.indexed_ambient_mode_star_entropy_bound
    address M ambient hsupport hmarginal hinj mode x hx E
  intro h hh
  apply hE h
  simpa only [admissible, MME.DWZAmbientStarCount.tables,
    MME.DWZAmbientStarCount.Admissible, Finset.mem_filter, Finset.mem_univ,
    true_and] using hh

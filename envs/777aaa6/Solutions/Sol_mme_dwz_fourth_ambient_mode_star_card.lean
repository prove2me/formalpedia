-- Prove2me | solution 1 for mme_dwz_fourth_ambient_mode_star_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T20:37:21.200716+00:00
-- url     : https://prove2.me/submissions/17619b48-07a7-4d65-a6d8-66e46044930e

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

open BigOperators
set_option maxRecDepth 100000 in
theorem MME.DWZAmbientStarCount.fourth_support_card :
    Fintype.card {sigma : Fin 3 → Fin 9 // (∑ i, (sigma i).val) = 8} = 45 := by
  decide

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

theorem solution (N : ℕ) (M : Fin 3 → Fin 9 → ℕ)
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
  exact MME.DWZAmbientStarCount.ambient_mode_star_card N M mode x hx


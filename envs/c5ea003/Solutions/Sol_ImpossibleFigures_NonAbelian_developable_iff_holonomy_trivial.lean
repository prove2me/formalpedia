-- Prove2me | solution 1 for ImpossibleFigures.NonAbelian.developable_iff_holonomy_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:45:04.62699+00:00
-- url     : https://prove2.me/submissions/e8d9c10e-37dc-4108-9c14-fe5eb63091c1

import Mathlib
import Definitions.Def_Geometry_NonAbelianHolonomy
open ImpossibleFigures.NonAbelian in
theorem solution {V E G : Type*} [Group G] {s t : E → V} (ω : E → G) (base : V)
    (hconn : ∀ v : V, ∃ l, IsWalk s t base v l) :
    Developable s t ω ↔ ∀ l, IsWalk s t base base l → hol ω l = 1 := by
  -- walks concatenate, and holonomy is anti-multiplicative along concatenation
  have happ : ∀ {a b c : V} {l m : List (Bool × E)},
      IsWalk s t a b l → IsWalk s t b c m → IsWalk s t a c (l ++ m) := by
    intro a b c l m hl hm
    induction hl with
    | nil v => exact hm
    | cons h hw ih => exact IsWalk.cons h (ih hm)
  have hholapp : ∀ l m : List (Bool × E), hol ω (l ++ m) = hol ω m * hol ω l := by
    intro l m
    induction l with
    | nil => simp [hol]
    | cons p l ih =>
      show hol ω (l ++ m) * stepHol ω p = hol ω m * (hol ω l * stepHol ω p)
      rw [ih, mul_assoc]
  -- reversing a walk inverts its holonomy
  have hrev : ∀ {a b : V} {l : List (Bool × E)}, IsWalk s t a b l →
      IsWalk s t b a (l.map revStep).reverse ∧ hol ω (l.map revStep).reverse = (hol ω l)⁻¹ := by
    intro a b l hl
    induction hl with
    | nil v => exact ⟨IsWalk.nil v, by simp [hol]⟩
    | @cons a b p l h hw ih =>
      obtain ⟨d, e⟩ := p
      rw [List.map_cons, List.reverse_cons]
      refine ⟨happ ih.1 (IsWalk.cons ?_ ?_), ?_⟩
      · cases d <;> rfl
      · cases d
        · show IsWalk s t (t e) a []
          have : t e = a := h
          rw [this]
          exact IsWalk.nil a
        · show IsWalk s t (s e) a []
          have : s e = a := h
          rw [this]
          exact IsWalk.nil a
      · rw [hholapp, ih.2]
        show (1 * stepHol ω (revStep (d, e))) * (hol ω l)⁻¹ = (hol ω l * stepHol ω (d, e))⁻¹
        cases d <;> simp [revStep, stepHol, mul_inv_rev]
  constructor
  · -- a developable connection has holonomy `K b (K a)⁻¹` along every walk
    rintro ⟨K, hK⟩ l hl
    have hgen : ∀ {a b : V} {l : List (Bool × E)}, IsWalk s t a b l → hol ω l = K b * (K a)⁻¹ := by
      intro a b l hl
      induction hl with
      | nil v => simp [hol]
      | @cons a b p l h hw ih =>
        show hol ω l * stepHol ω p = K b * (K a)⁻¹
        rw [ih]
        obtain ⟨d, e⟩ := p
        cases d
        · have ha : t e = a := h
          show K b * (K (s e))⁻¹ * (ω e)⁻¹ = K b * (K a)⁻¹
          rw [hK e, ← ha]
          group
        · have ha : s e = a := h
          show K b * (K (t e))⁻¹ * ω e = K b * (K a)⁻¹
          rw [hK e, ← ha]
          group
    rw [hgen hl, mul_inv_cancel]
  · -- trivial holonomy: the holonomy along any chosen path from `base` is a potential
    intro hclosed
    choose L hL using hconn
    refine ⟨fun v => hol ω (L v), fun e => ?_⟩
    have hstep : IsWalk s t (s e) (t e) [(true, e)] := IsWalk.cons rfl (IsWalk.nil (t e))
    have hC := hclosed _ (happ (happ (hL (s e)) hstep) (hrev (hL (t e))).1)
    rw [hholapp, hholapp, (hrev (hL (t e))).2] at hC
    have hone : hol ω [(true, e)] = ω e := by simp [hol, stepHol]
    rw [hone, inv_mul_eq_one] at hC
    exact eq_mul_inv_of_mul_eq hC.symm

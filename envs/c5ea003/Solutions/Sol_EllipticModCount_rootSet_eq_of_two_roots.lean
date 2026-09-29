-- Prove2me | solution 1 for EllipticModCount.rootSet_eq_of_two_roots
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:09:51.075817+00:00
-- url     : https://prove2.me/submissions/7e008674-ed7d-4bd7-ac10-1ae847959fd9

import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
open EllipticModCount Finset in
theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a b r s : F}
    (hd : disc a b ≠ 0)
    (hr : wRHS a b r = 0) (hs : wRHS a b s = 0) (hrs : r ≠ s) :
    rootSet a b = {r, s, -(r + s)} ∧ (rootSet a b).card = 3 := by
  unfold wRHS at hr hs
  -- Vieta: `a = -(r² + rs + s²)`, `b = rs(r + s)`
  have hrs' : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have ha : a = -(r ^ 2 + r * s + s ^ 2) := by
    have : (r - s) * (r ^ 2 + r * s + s ^ 2 + a) = (r - s) * 0 := by
      linear_combination hr - hs
    have := mul_left_cancel₀ hrs' this
    linear_combination this
  have hb : b = r * s * (r + s) := by
    rw [ha] at hr
    linear_combination hr
  have hfac : ∀ x, wRHS a b x = (x - r) * (x - s) * (x + (r + s)) := by
    intro x
    unfold wRHS
    rw [ha, hb]
    ring
  -- the discriminant is `-(r - s)²(2r + s)²(r + 2s)²`
  have hdisc : disc a b = -((r - s) * (2 * r + s) * (r + 2 * s)) ^ 2 := by
    unfold disc
    rw [ha, hb]
    ring
  have hprod : (r - s) * (2 * r + s) * (r + 2 * s) ≠ 0 := by
    intro h0
    apply hd
    rw [hdisc, h0]
    ring
  have h1 : 2 * r + s ≠ 0 := fun h0 => hprod (by rw [h0]; ring)
  have h2 : r + 2 * s ≠ 0 := fun h0 => hprod (by rw [h0]; ring)
  have hrt : r ≠ -(r + s) := fun h0 => h1 (by linear_combination h0)
  have hst : s ≠ -(r + s) := fun h0 => h2 (by linear_combination h0)
  have hset : rootSet a b = {r, s, -(r + s)} := by
    ext x
    simp only [rootSet, mem_filter, mem_univ, true_and, hfac, mem_insert, mem_singleton,
      mul_eq_zero, sub_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by linear_combination h))
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (by rw [h]; ring)
  refine ⟨hset, ?_⟩
  rw [hset]
  exact card_eq_three.mpr ⟨r, s, -(r + s), hrs, hrt, hst, rfl⟩

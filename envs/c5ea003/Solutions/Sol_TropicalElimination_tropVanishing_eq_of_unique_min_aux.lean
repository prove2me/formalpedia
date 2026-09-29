-- Prove2me | solution 1 for TropicalElimination.tropVanishing_eq_of_unique_min_aux
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:53:19.40426+00:00
-- url     : https://prove2.me/submissions/5ca7c9f0-6650-49d3-9575-5158c4d59fd0

import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination
open TropicalElimination in
theorem solution {E : Type*} [Nonempty E] [DecidableEq E] (c : E → TT) {x y : E → TT}
    (hx : x ∈ tropVanishing c) (hy : y ∈ tropVanishing c) {e i₀ : E}
    (hi₀e : i₀ ≠ e) (hxye : x e = y e)
    (hmin : ∀ j, j ≠ i₀ →
      c i₀ + min (x i₀) (y i₀) < c j + (if j = e then ⊤ else min (x j) (y j)))
    (hle : x i₀ ≤ y i₀) : x i₀ = y i₀ := by
  by_contra hne
  have hlt : x i₀ < y i₀ := lt_of_le_of_ne hle hne
  have hmn : min (x i₀) (y i₀) = x i₀ := min_eq_left hle
  -- the minimum value is finite (compare with the `⊤` entry at `e`)
  have hfin : c i₀ + x i₀ < ⊤ := by
    have := hmin e hi₀e.symm
    rw [if_pos rfl, add_top, hmn] at this
    exact this
  have hci : c i₀ ≠ ⊤ := fun h => by
    rw [h, top_add] at hfin
    exact lt_irrefl _ hfin
  -- the witness for `x` at `i₀` must be `e`
  obtain ⟨j, hji, hj⟩ := hx i₀
  by_cases hje : j = e
  · rw [hje] at hj
    -- then the witness for `y` at `e` is either `i₀` (forcing `y i₀ ≤ x i₀`) or breaks minimality
    obtain ⟨j', hj'e, hj'⟩ := hy e
    rw [← hxye] at hj'
    by_cases hj'i : j' = i₀
    · rw [hj'i] at hj'
      have h3 : c i₀ + y i₀ ≤ c i₀ + x i₀ := hj'.trans hj
      rw [WithTop.add_le_add_iff_left hci] at h3
      exact absurd h3 (not_le.mpr hlt)
    · have hm := hmin j' hj'i
      rw [if_neg hj'e, hmn] at hm
      have h4 : c j' + min (x j') (y j') ≤ c j' + y j' := add_le_add_right (min_le_right _ _) _
      exact absurd (hm.trans_le (h4.trans (hj'.trans hj))) (lt_irrefl _)
  · have hm := hmin j hji
    rw [if_neg hje, hmn] at hm
    have h4 : c j + min (x j) (y j) ≤ c j + x j := add_le_add_right (min_le_left _ _) _
    exact absurd (hm.trans_le (h4.trans hj)) (lt_irrefl _)

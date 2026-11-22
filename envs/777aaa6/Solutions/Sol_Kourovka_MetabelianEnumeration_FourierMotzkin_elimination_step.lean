-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.elimination_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:40.257176+00:00
-- url     : https://prove2.me/submissions/5609f694-081c-4242-9c1c-c18eb5ca5f72

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_Row_eval_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_Row_eval_combine
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_finite_interval
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_lower_constraint
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_upper_constraint
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_pair_constraint
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_satisfies_eliminate_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {n : ℕ} (rows : List (Row (n + 1)))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin n → K) :
    Satisfies (eliminate rows) x ↔ ∃ t : K, Satisfies rows (Fin.cons t x) := by
  rw [satisfies_eliminate_iff]
  constructor
  · rintro ⟨hz, hp⟩
    let lower : List K := (negatives rows).map fun r => -r.tail.eval x / (r.head : K)
    let upper : List K := (positives rows).map fun r => -r.tail.eval x / (r.head : K)
    have hcross : ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u := by
      intro l hl u hu
      obtain ⟨lr, hlr, rfl⟩ := List.mem_map.mp hl
      obtain ⟨ur, hur, rfl⟩ := List.mem_map.mp hu
      obtain ⟨hlmem, hlneg⟩ := List.mem_filter.mp hlr
      obtain ⟨humem, hupos⟩ := List.mem_filter.mp hur
      have hlneg' : lr.head < 0 := of_decide_eq_true hlneg
      have hupos' : 0 < ur.head := of_decide_eq_true hupos
      have hlcast : (lr.head : K) < 0 := by exact_mod_cast hlneg'
      have hucast : (0 : K) < ur.head := by exact_mod_cast hupos'
      apply (pair_constraint hlcast hucast).mp
      simpa only [Row.eval_combine] using hp lr hlmem hlneg' ur humem hupos'
    obtain ⟨t, htlow, htup⟩ := (finite_interval lower upper).mpr hcross
    refine ⟨t, ?_⟩
    intro r hr
    rw [Row.eval_cons]
    rcases lt_trichotomy r.head 0 with hneg | hzero | hpos
    · have hcast : (r.head : K) < 0 := by exact_mod_cast hneg
      apply (lower_constraint hcast).mpr
      exact htlow _ (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa⟩, rfl⟩)
    · simpa only [hzero, Rat.cast_zero, zero_mul, zero_add] using hz r hr hzero
    · have hcast : (0 : K) < r.head := by exact_mod_cast hpos
      apply (upper_constraint hcast).mpr
      exact htup _ (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa⟩, rfl⟩)
  · rintro ⟨t, ht⟩
    constructor
    · intro r hr hzero
      have h := ht r hr
      simpa only [Row.eval_cons, hzero, Rat.cast_zero, zero_mul, zero_add] using h
    · intro l hl hlneg u hu hupos
      have hlcast : (l.head : K) < 0 := by exact_mod_cast hlneg
      have hucast : (0 : K) < u.head := by exact_mod_cast hupos
      rw [Row.eval_combine]
      apply (pair_constraint hlcast hucast).mpr
      exact ((lower_constraint hlcast).mp (by simpa only [Row.eval_cons] using ht l hl)).trans
        ((upper_constraint hucast).mp (by simpa only [Row.eval_cons] using ht u hu))
end Kourovka.MetabelianEnumeration.FourierMotzkin

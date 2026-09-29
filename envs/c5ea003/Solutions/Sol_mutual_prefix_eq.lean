-- Prove2me | solution 1 for mutual_prefix_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:56:00.05178+00:00
-- url     : https://prove2.me/submissions/f699d2bc-3a14-43b1-a64f-9f0debf93be6

-- Sol generated from Cryptography/BiOrderSeparation.lean
import Mathlib
import Definitions.Def_Cryptography_BiOrderSeparation

/-!
# Bounded right traces of binary words

This module supplies the finite-word separation facts used by the universal
poset and coherent-composition developments.  A word is a finite binary list.
Its bounded right trace consists of its extensions whose total length is at
most the bound.  Two words that themselves lie under the bound are determined
by these traces.
-/





theorem solution{α : Type*} {x y : List α}
    (hxy : ∃ t, x = y ++ t) (hyx : ∃ t, y = x ++ t) : x = y := by
  obtain ⟨t, ht⟩ := hxy
  obtain ⟨u, hu⟩ := hyx
  have hxyLen : y.length ≤ x.length := by
    rw [ht, List.length_append]
    omega
  have hyxLen : x.length ≤ y.length := by
    rw [hu, List.length_append]
    omega
  have hlen : x.length = y.length := Nat.le_antisymm hyxLen hxyLen
  have htLen : t.length = 0 := by
    have := congrArg List.length ht
    simp only [List.length_append] at this
    omega
  have htNil : t = [] := by
    cases t with
    | nil => rfl
    | cons a t => simp at htLen
  simpa [htNil] using ht

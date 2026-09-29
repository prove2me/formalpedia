-- Prove2me | solution 1 for rightTrace_eq_imp_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:58:38.328716+00:00
-- url     : https://prove2.me/submissions/b50da779-b350-471b-af61-44ffb9199151

-- Sol generated from Cryptography/BiOrderSeparation.lean
import Mathlib
import Definitions.Def_Cryptography_BiOrderSeparation
import Theorems.Thm_mutual_prefix_eq

/-!
# Bounded right traces of binary words

This module supplies the finite-word separation facts used by the universal
poset and coherent-composition developments.  A word is a finite binary list.
Its bounded right trace consists of its extensions whose total length is at
most the bound.  Two words that themselves lie under the bound are determined
by these traces.
-/





theorem solution{R : ℕ} {x y : Word}
    (hx : x.length ≤ R) (hy : y.length ≤ R)
    (htrace : rightTraceWord R x = rightTraceWord R y) : x = y := by
  have hxx : x ∈ rightTraceWord R x := ⟨hx, [], by simp⟩
  have hyy : y ∈ rightTraceWord R y := ⟨hy, [], by simp⟩
  rw [htrace] at hxx
  rw [← htrace] at hyy
  exact mutual_prefix_eq hxx.2 hyy.2

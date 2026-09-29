-- Prove2me | solution 1 for ReversibleElementary.single_coordinate_rule_bijective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:00:00.968627+00:00
-- url     : https://prove2.me/submissions/d161d5d0-129b-477e-a7ba-fbe9cc9126cd

-- Sol generated from Novelty/ReversibleElementary.lean
import Mathlib
import Definitions.Def_Novelty_ReversibleElementary

/-!
# Reversible elementary cellular automata

This file gives a finite, machine-checked correction to the proposed “local-rule
permutation” picture.  An elementary local rule has type `Bool³ → Bool`, so it
is not a permutation of the eight neighborhoods.  Reversibility concerns the
induced global map on configurations.

We prove a chain of structural results for the six projection/complement rules,
then exhaustively classify the rules which are bijective on cyclic configurations
of sizes 1 through 4.  The finite test leaves exactly Wolfram rules
15, 51, 85, 170, 204, and 240.  Since each of these six is proved reversible on
every nonempty finite cycle, the test also gives a certified obstruction of
period at most four for every other elementary rule.
-/

open ReversibleElementary










/-- Successor followed by predecessor returns the original cyclic index. -/
theorem leftIdx_rightIdx {n : ℕ} (hn : 0 < n) (i : Fin n) :
    leftIdx hn (rightIdx hn i) = i := by
  apply Fin.ext
  simp [leftIdx, rightIdx]
  rcases n with _ | _ | n <;> norm_num at *
  simp +arith +decide
  norm_num [(by ring : n + i + 2 = n + 2 + i)]
  exact Fin.is_le i


/-- Predecessor followed by successor also returns the original index. -/
theorem rightIdx_leftIdx {n : ℕ} (hn : 0 < n) (i : Fin n) :
    rightIdx hn (leftIdx hn i) = i := by
  rcases n with _ | _ | n <;> norm_num [Fin.ext_iff, leftIdx, rightIdx] at *
  · contradiction
  · norm_num [add_assoc, Nat.mod_eq_of_lt]















/-! ## Alphabet-independent reversible dynamics

The elementary classification above is binary, but its positive mechanism does
not depend on the alphabet being Boolean. A local rule that reads one site and
then applies an alphabet permutation is reversible over every alphabet.
-/









open ReversibleElementary in
theorem solution{α : Type*} {n : ℕ} (hn : 0 < n)
    (f : LocalRuleOver α) (e : Equiv.Perm α)
    (hf : (∀ l c r, f l c r = e l) ∨
      (∀ l c r, f l c r = e c) ∨
      (∀ l c r, f l c r = e r)) :
    Function.Bijective (globalMapOver f hn) := by
  rw [Function.bijective_iff_has_inverse]
  rcases hf with hl | hc | hr
  · refine ⟨(fun x i => e.symm (x (rightIdx hn i))), ?_, ?_⟩
    · intro x
      funext i
      simp only [globalMapOver, hl, Equiv.symm_apply_apply, leftIdx_rightIdx]
    · intro x
      funext i
      simp only [globalMapOver, hl, rightIdx_leftIdx, Equiv.apply_symm_apply]
  · refine ⟨(fun x i => e.symm (x i)), ?_, ?_⟩
    · intro x
      funext i
      simp only [globalMapOver, hc, Equiv.symm_apply_apply]
    · intro x
      funext i
      simp only [globalMapOver, hc, Equiv.apply_symm_apply]
  · refine ⟨(fun x i => e.symm (x (leftIdx hn i))), ?_, ?_⟩
    · intro x
      funext i
      simp only [globalMapOver, hr, Equiv.symm_apply_apply, rightIdx_leftIdx]
    · intro x
      funext i
      simp only [globalMapOver, hr, leftIdx_rightIdx, Equiv.apply_symm_apply]

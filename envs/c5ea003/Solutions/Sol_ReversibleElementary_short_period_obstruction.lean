-- Prove2me | solution 1 for ReversibleElementary.short_period_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:00:00.447817+00:00
-- url     : https://prove2.me/submissions/5ea6805d-133b-44a5-b52c-c7d1893e4f1c

-- Sol generated from Novelty/ReversibleElementary.lean
import Mathlib
import Definitions.Def_Novelty_ReversibleElementary
import Theorems.Thm_ReversibleElementary_reversible_small_cycles_iff

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



























/-! ## Alphabet-independent reversible dynamics

The elementary classification above is binary, but its positive mechanism does
not depend on the alphabet being Boolean. A local rule that reads one site and
then applies an alphabet permutation is reversible over every alphabet.
-/









open ReversibleElementary in
theorem solution(w : Fin 256)
    (hw : w ∉ ([15, 51, 85, 170, 204, 240] : List (Fin 256))) :
    ∃ n ∈ ({1, 2, 3, 4} : Finset ℕ), ¬ ReversibleOn n w := by
  have hw' : ¬ (ReversibleOn 1 w ∧ ReversibleOn 2 w ∧
      ReversibleOn 3 w ∧ ReversibleOn 4 w) := by
    intro h
    exact hw ((reversible_small_cycles_iff w).mp h)
  have hor : ¬ ReversibleOn 1 w ∨ ¬ ReversibleOn 2 w ∨
      ¬ ReversibleOn 3 w ∨ ¬ ReversibleOn 4 w := by
    tauto
  rcases hor with h1 | h2 | h3 | h4
  · exact ⟨1, by decide, h1⟩
  · exact ⟨2, by decide, h2⟩
  · exact ⟨3, by decide, h3⟩
  · exact ⟨4, by decide, h4⟩

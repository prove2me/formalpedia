-- Prove2me | solution 1 for ReversibleElementary.reversible_small_cycles_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:56:58.033703+00:00
-- url     : https://prove2.me/submissions/37cdd9c7-bf31-4696-92d1-53d86a136e2c

-- Sol generated from Novelty/ReversibleElementary.lean
import Mathlib
import Definitions.Def_Novelty_ReversibleElementary
import Theorems.Thm_ReversibleElementary_six_rules_universally_reversible

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
theorem solution(w : Fin 256) :
    (ReversibleOn 1 w ∧ ReversibleOn 2 w ∧ ReversibleOn 3 w ∧ ReversibleOn 4 w) ↔
      w ∈ ([15, 51, 85, 170, 204, 240] : List (Fin 256)) := by
  constructor
  · fin_cases w <;> decide
  · intro hw
    have hu := six_rules_universally_reversible w hw
    constructor
    · simpa [ReversibleOn] using hu 1 (by omega)
    constructor
    · simpa [ReversibleOn] using hu 2 (by omega)
    constructor
    · simpa [ReversibleOn] using hu 3 (by omega)
    · simpa [ReversibleOn] using hu 4 (by omega)

-- Prove2me | Theorems.Thm_ReversibleElementary_reversible_small_cycles_iff
-- name    : ReversibleElementary.reversible_small_cycles_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:28:55.875725+00:00
-- url     : https://prove2.me/theorems/1359a127-b09b-428e-959a-9db74a1094d6
-- title:
--   Exhaustive finite calculation: bijectivity on cycles 1 through 4 leaves exactly six rules.
-- statement:
--   Exhaustive finite calculation: bijectivity on cycles 1 through 4 leaves exactly six rules.
--
--   ```lean
--   theorem ReversibleElementary.reversible_small_cycles_iff(w : Fin 256) :
--       (ReversibleOn 1 w ∧ ReversibleOn 2 w ∧ ReversibleOn 3 w ∧ ReversibleOn 4 w) ↔
--         w ∈ ([15, 51, 85, 170, 204, 240] : List (Fin 256)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReversibleElementary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReversibleElementary.lean#L170

-- Thm stub generated from Novelty/ReversibleElementary.lean
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

theorem ReversibleElementary.reversible_small_cycles_iff(w : Fin 256) :
    (ReversibleOn 1 w ∧ ReversibleOn 2 w ∧ ReversibleOn 3 w ∧ ReversibleOn 4 w) ↔
      w ∈ ([15, 51, 85, 170, 204, 240] : List (Fin 256)) := by sorry

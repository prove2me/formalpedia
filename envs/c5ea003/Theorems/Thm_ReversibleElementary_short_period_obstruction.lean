-- Prove2me | Theorems.Thm_ReversibleElementary_short_period_obstruction
-- name    : ReversibleElementary.short_period_obstruction
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:29:05.862333+00:00
-- url     : https://prove2.me/theorems/9fff65a1-765f-4efe-8e20-1b9f4e21f7fd
-- title:
--   Every elementary rule outside the six-rule list already fails injectivity or
-- statement:
--   Every elementary rule outside the six-rule list already fails injectivity or
--   surjectivity on a cycle of length at most four.
--
--   ```lean
--   theorem ReversibleElementary.short_period_obstruction(w : Fin 256)
--       (hw : w ∉ ([15, 51, 85, 170, 204, 240] : List (Fin 256))) :
--       ∃ n ∈ ({1, 2, 3, 4} : Finset ℕ), ¬ ReversibleOn n w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReversibleElementary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReversibleElementary.lean#L186

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

theorem ReversibleElementary.short_period_obstruction(w : Fin 256)
    (hw : w ∉ ([15, 51, 85, 170, 204, 240] : List (Fin 256))) :
    ∃ n ∈ ({1, 2, 3, 4} : Finset ℕ), ¬ ReversibleOn n w := by sorry

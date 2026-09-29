-- Prove2me | Theorems.Thm_ReversibleElementary_six_rules_universally_reversible
-- name    : ReversibleElementary.six_rules_universally_reversible
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:29:04.254534+00:00
-- url     : https://prove2.me/theorems/b4bab357-8d2f-42c6-859b-6580e02bceb1
-- title:
--   Each of the six elementary projection/complement rules is reversible on every cycle.
-- statement:
--   Each of the six elementary projection/complement rules is reversible on every cycle.
--
--   ```lean
--   theorem ReversibleElementary.six_rules_universally_reversible:
--       ∀ w ∈ ([15, 51, 85, 170, 204, 240] : List (Fin 256)), UniversallyReversible w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReversibleElementary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReversibleElementary.lean#L136

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

theorem ReversibleElementary.six_rules_universally_reversible:
    ∀ w ∈ ([15, 51, 85, 170, 204, 240] : List (Fin 256)), UniversallyReversible w := by sorry

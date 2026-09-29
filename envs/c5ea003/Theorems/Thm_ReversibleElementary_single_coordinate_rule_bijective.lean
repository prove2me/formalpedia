-- Prove2me | Theorems.Thm_ReversibleElementary_single_coordinate_rule_bijective
-- name    : ReversibleElementary.single_coordinate_rule_bijective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:29:04.588577+00:00
-- url     : https://prove2.me/theorems/c798c0ae-8c25-4662-a36b-5d19480c7242
-- title:
--   A radius-one rule obtained by applying an alphabet permutation to any one
-- statement:
--   A radius-one rule obtained by applying an alphabet permutation to any one
--   of its three inputs has bijective dynamics on every nonempty finite cycle.
--
--   ```lean
--   theorem ReversibleElementary.single_coordinate_rule_bijective{α : Type*} {n : ℕ} (hn : 0 < n)
--       (f : LocalRuleOver α) (e : Equiv.Perm α)
--       (hf : (∀ l c r, f l c r = e l) ∨
--         (∀ l c r, f l c r = e c) ∨
--         (∀ l c r, f l c r = e r)) :
--       Function.Bijective (globalMapOver f hn) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReversibleElementary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReversibleElementary.lean#L283

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



























/-! ## Alphabet-independent reversible dynamics

The elementary classification above is binary, but its positive mechanism does
not depend on the alphabet being Boolean. A local rule that reads one site and
then applies an alphabet permutation is reversible over every alphabet.
-/

theorem ReversibleElementary.single_coordinate_rule_bijective{α : Type*} {n : ℕ} (hn : 0 < n)
    (f : LocalRuleOver α) (e : Equiv.Perm α)
    (hf : (∀ l c r, f l c r = e l) ∨
      (∀ l c r, f l c r = e c) ∨
      (∀ l c r, f l c r = e r)) :
    Function.Bijective (globalMapOver f hn) := by sorry

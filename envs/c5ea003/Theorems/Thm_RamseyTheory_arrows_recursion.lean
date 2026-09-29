-- Prove2me | Theorems.Thm_RamseyTheory_arrows_recursion
-- name    : RamseyTheory.arrows_recursion
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:01:11.726205+00:00
-- url     : https://prove2.me/theorems/7fead537-552c-4075-848b-4f03e515d734
-- title:
--   Erdős–Szekeres / binomial upper bound.
-- statement:
--   **Erdős–Szekeres / binomial upper bound.**
--   For all `s t`, `C(s+t, s) → (s+1, t+1)`, i.e. `R(s+1, t+1) ≤ C(s+t, s)`.
--
--   The proof is a double induction on `s` and `t`.  The base cases use that a single
--   vertex is both a red and a blue `1`‑clique; the inductive step combines the two
--   smaller instances via `arrows_step`, the cardinalities adding up by Pascal's
--   rule `C(s+t, s) = C(s-1+t, s-1) + C(s+t-1, s)`.
--
--   ```lean
--   theorem RamseyTheory.arrows_recursion(s t : ℕ) : Arrows ((s + t).choose s) (s + 1) (t + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Combinatorics/Ramsey.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Combinatorics/Ramsey.lean#L102

-- Thm stub generated from Applications/Combinatorics/Ramsey.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_Ramsey
/-
# Finite two‑colour Ramsey theory

This file develops the elementary theory of finite two‑colour Ramsey numbers,
culminating in the exact value `R(3,3) = 6` and the Erdős–Szekeres binomial
upper bound `R(s+1, t+1) ≤ C(s+t, s)`.

A *two‑colouring* of a complete graph is encoded by a single `SimpleGraph G`:
the edges of `G` are the **red** edges and the edges of its complement `Gᶜ`
are the **blue** edges.  A red clique is then a clique of `G` and a blue clique
is a clique of `Gᶜ`.

The central relation is the *arrow* relation `Arrows n s t`
(classically written `n → (s, t)`): every red/blue colouring of any vertex set
of size at least `n` contains a red `s`‑clique or a blue `t`‑clique.
-/


open scoped Classical
open SimpleGraph Finset

open RamseyTheory

/-! ## Core combinatorial objects -/



/-! ## Monotonicity -/


/-! ## The Erdős–Szekeres recursion -/

theorem RamseyTheory.arrows_recursion(s t : ℕ) : Arrows ((s + t).choose s) (s + 1) (t + 1) := by sorry

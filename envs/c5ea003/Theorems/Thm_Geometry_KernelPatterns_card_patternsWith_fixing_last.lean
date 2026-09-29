-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_card_patternsWith_fixing_last
-- name    : Geometry.KernelPatterns.card_patternsWith_fixing_last
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:18:21.926748+00:00
-- url     : https://prove2.me/theorems/c26b7a1c-d3df-4bbb-a721-5c5a0948daaa
-- title:
--   Patterns on `Fin (n+1)` fixing the last index correspond to patterns on
-- statement:
--   Patterns on `Fin (n+1)` fixing the last index correspond to patterns on
--   `Fin n` with one block fewer.
--
--   ```lean
--   theorem Geometry.KernelPatterns.card_patternsWith_fixing_last(n k : ℕ) :
--       ((patternsWith (n + 1) (k + 1)).filter fun p => p (Fin.last n) = Fin.last n).card
--         = (patternsWith n k).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Stirling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Stirling.lean#L186

-- Thm stub generated from Geometry/KernelPatterns/Stirling.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Stirling

/-!
# Kernel patterns with a prescribed number of blocks are the Stirling numbers

Mathlib defines the Stirling numbers of the second kind `Nat.stirlingSecond`
purely by their recursion.  Here we prove that they really do count kernel
patterns: the number of equality patterns of `n`-tuples having exactly `k`
distinct values is `Nat.stirlingSecond n k`
(`card_patternsWith_eq_stirlingSecond`).

The proof is a structural induction implemented by an explicit
restriction/extension dictionary between patterns on `Fin (n+1)` and patterns on
`Fin n`:

* `restr p` — delete the last index;
* `extend q a` — re-attach a last index whose representative is `a`;
* `extend_restr`, `restr_extend` — these are mutually inverse.

Deleting the last index either destroys a singleton block (`p` fixes the last
index) or leaves the block structure unchanged (`p` sends it into one of the
`k` existing blocks), which is exactly the Stirling recursion
`S(n+1, k+1) = (k+1) * S(n, k+1) + S(n, k)`.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ}

/-! ### A pointwise characterisation of patterns -/



/-! ### Deleting and re-attaching the last index -/










/-! ### How the block count changes -/





/-! ### The Stirling recursion -/

theorem Geometry.KernelPatterns.card_patternsWith_fixing_last(n k : ℕ) :
    ((patternsWith (n + 1) (k + 1)).filter fun p => p (Fin.last n) = Fin.last n).card
      = (patternsWith n k).card := by sorry

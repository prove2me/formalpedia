-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_card_patterns_eq_bell
-- name    : Geometry.KernelPatterns.card_patterns_eq_bell
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:16:02.651787+00:00
-- url     : https://prove2.me/theorems/fabd0c0e-0afd-488d-9384-93a725fdc87a
-- title:
--   Kernel patterns of `n`-tuples are counted by the `n`-th Bell number.
-- statement:
--   **Kernel patterns of `n`-tuples are counted by the `n`-th Bell number.**
--
--   ```lean
--   theorem Geometry.KernelPatterns.card_patterns_eq_bell: ∀ n : ℕ, (patterns n n).card = Nat.bell n
--     := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/BellRecursion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/BellRecursion.lean#L234

-- Thm stub generated from Geometry/KernelPatterns/BellRecursion.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_BellRecursion
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling

/-!
# Kernel patterns are counted by the Bell numbers, for every `n`

`Geometry.KernelPatterns.Bell` verified the first six values of the
pattern-counting sequence by `decide`.  Here we prove the general statement:

* `card_patterns_eq_bell` — `#(patterns n n) = Nat.bell n` for every `n`;
* `card_setoid_fin_eq_bell` — equivalently, the number of equivalence relations
  (set partitions) on an `n`-element set is `Nat.bell n`.

The proof runs the Bell recursion `B(n+1) = Σ_i C(n,i) B(n-i)` on the pattern
model.  A pattern of `Fin (n+1)` is split into

* the block `S` of the last index (a subset of `Fin n`), and
* the induced partition of the complement `Sᶜ`,

the second datum being encoded as an abstract `Setoid ↥Sᶜ`; the inverse
construction turns a setoid into a pattern by taking the kernel of the map
`blockFun` that collapses the last block to `none` and sends everything else to
its class.  Summing the fibre counts over all subsets `S` and grouping by
`|S|` produces exactly Mathlib's defining recursion for `Nat.bell`.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-! ### The last block of a pattern -/



/-! ### From a setoid on the complement back to a pattern -/










/-! ### The fibre of `lastBlk` over a subset -/




/-! ### Counting -/

theorem Geometry.KernelPatterns.card_patterns_eq_bell: ∀ n : ℕ, (patterns n n).card = Nat.bell n
  := by sorry

-- Prove2me | solution 1 for Geometry.KernelPatterns.card_setoid_of_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:31:00.330811+00:00
-- url     : https://prove2.me/submissions/66cb5cf4-1edf-494a-801c-00c0ee854262

-- Sol generated from Geometry/KernelPatterns/BellRecursion.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
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


lemma card_setoid_eq_card_patterns (m : ℕ) :
    Nat.card (Setoid (Fin m)) = (patterns m m).card := by
  rw [← Nat.card_eq_finsetCard, Nat.card_congr (patternsEquivSetoid m)]









open Geometry.KernelPatterns in
theorem solution{α : Type*} [Fintype α] :
    Nat.card (Setoid α) = (patterns (Fintype.card α) (Fintype.card α)).card := by
  rw [Nat.card_congr (setoidCongr (Fintype.equivFin α)), card_setoid_eq_card_patterns]

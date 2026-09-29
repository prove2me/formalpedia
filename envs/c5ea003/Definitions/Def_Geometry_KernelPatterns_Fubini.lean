-- Prove2me | Definitions.Def_Geometry_KernelPatterns_Fubini
-- name    : Geometry_KernelPatterns_Fubini
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:10.195755+00:00
-- url     : https://prove2.me/theorems/d2717e4c-b4d5-4876-ab6a-16ab07b32f07
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_Fubini
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.Fubini`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/Fubini.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Faces
import Definitions.Def_Geometry_KernelPatterns_Stirling

/-!
# The Fubini (ordered Bell) formula for faces of the braid arrangement

`Faces.lean` introduced the *ordered pattern* `rank v` of a tuple and showed it
is a complete invariant of the face of the braid arrangement spanned by `v`.
This file counts the ordered patterns exactly:

`#(ordPatterns n) = ∑_{k ≤ n} S(n, k) · k!`,

the ordered Bell (Fubini) numbers `1, 1, 3, 13, 75, 541` (OEIS A000670), where
`S(n, k) = Nat.stirlingSecond n k` counts the kernel patterns with `k` blocks
(`Stirling.lean`).  Geometrically: every face of the braid arrangement is
obtained from a flat (a kernel pattern, i.e. a set partition into `k` blocks) by
choosing one of the `k!` linear orders of its blocks.

The proof fibres `ordPatterns n` first over the number of blocks and then over
the underlying kernel pattern, and identifies each fibre with `Equiv.Perm (Fin k)`
by transporting along the order isomorphism `Fin k ≃o` (block representatives).

Main results:
* `card_reps` — the block representatives biject with the distinct values.
* `rank_val_eq_of_surjective` — for a *surjective* `v : Fin n → Fin k` the rank
  function is the tuple itself; this is the rigidity statement that makes the
  fibres rigid.
* `card_fibre_ordPatterns` — the ordered patterns refining a fixed kernel
  pattern with `k` blocks number exactly `k!`.
* `card_ordPatternsWith` — `#{faces with k blocks} = S(n,k) · k!`.
* `card_ordPatterns_eq_sum_stirlingSecond` — the Fubini formula.
-/

namespace Geometry.KernelPatterns

open Finset

variable {n k : ℕ} {X : Type*} [LinearOrder X]

/-! ### Block representatives -/

/-- The set of block representatives of a tuple: the indices of first
occurrences. -/
def reps (v : Fin n → X) : Finset (Fin n) := univ.filter fun j => pat v j = j





/-! ### Rank versus the number of blocks -/




/-! ### The fibres of `pat` on ordered patterns -/


/-! ### The Fubini formula -/

/-- Ordered patterns (faces) with exactly `k` blocks. -/
def ordPatternsWith (n k : ℕ) : Finset (Fin n → Fin n) :=
  (ordPatterns n).filter fun r => (univ.image r).card = k





/-! ### Faces versus chambers and flats -/



end Geometry.KernelPatterns



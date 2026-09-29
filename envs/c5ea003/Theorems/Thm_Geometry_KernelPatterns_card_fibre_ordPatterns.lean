-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_card_fibre_ordPatterns
-- name    : Geometry.KernelPatterns.card_fibre_ordPatterns
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:20:51.449254+00:00
-- url     : https://prove2.me/theorems/dca67726-602e-47a4-a629-3bf5e84586c3
-- title:
--   Each flat carries exactly `k!` faces.
-- statement:
--   **Each flat carries exactly `k!` faces.**  The ordered patterns refining a
--   fixed kernel pattern `p` with `k` blocks are in bijection with the linear orders
--   of the blocks.
--
--   ```lean
--   theorem Geometry.KernelPatterns.card_fibre_ordPatterns{p : Fin n → Fin n} (hp : pat p = p)
--       (hk : (univ.image p).card = k) :
--       ((ordPatterns n).filter fun r => pat r = p).card = k.factorial := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Fubini.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Fubini.lean#L117

-- Thm stub generated from Geometry/KernelPatterns/Fubini.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Faces
import Definitions.Def_Geometry_KernelPatterns_Fubini
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

open Geometry.KernelPatterns

open Finset

variable {n k : ℕ} {X : Type*} [LinearOrder X]

/-! ### Block representatives -/






/-! ### Rank versus the number of blocks -/




/-! ### The fibres of `pat` on ordered patterns -/

theorem Geometry.KernelPatterns.card_fibre_ordPatterns{p : Fin n → Fin n} (hp : pat p = p)
    (hk : (univ.image p).card = k) :
    ((ordPatterns n).filter fun r => pat r = p).card = k.factorial := by sorry

-- Prove2me | Theorems.Thm_MultiverseFrameCounting_card_cacc_pairs
-- name    : MultiverseFrameCounting.card_cacc_pairs
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:38:58.691574+00:00
-- url     : https://prove2.me/theorems/d6792211-24f2-4438-a7e4-82060b937014
-- title:
--   Exact size of the forcing relation.
-- statement:
--   **Exact size of the forcing relation.**  The control frame built from `n`
--   independent buttons and `m` independent switches has exactly `3^n · 4^m`
--   accessibility pairs: `3` states per button (as in `sum_two_pow_card_powerset`) and
--   `4` per switch (its value before and after the extension are unconstrained).
--
--   ```lean
--   theorem MultiverseFrameCounting.card_cacc_pairs(n m : ℕ) :
--       ∑ v : CWorld (Fin n) (Fin m),
--           (Finset.univ.filter fun w : CWorld (Fin n) (Fin m) => cacc w v).card
--         = 3 ^ n * 4 ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/FrameCounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/FrameCounting.lean#L63

-- Thm stub generated from Logic/Multiverse/FrameCounting.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_FrameCounting
/-
# Counting the Finite Control Frames

A combinatorial companion to `Catalog/Logic/Multiverse/BooleanValuedRealization.lean`.

The finite pre-Boolean forcing frames used for the countermodels are assembled from
`n` independent buttons and `m` independent switches.  We compute their size
exactly:

* `sum_two_pow_card_powerset` — `∑_{t ⊆ s} 2^|t| = 3^|s|`, proved by induction on
  `s` (the enumerative heart: each element is either outside `t`, inside `t` but
  outside the ambient set, or in both);
* `card_cacc_pairs` — the frame with `n` buttons and `m` switches has exactly
  `3^n · 4^m` accessibility pairs, and (`card_worlds`) `2^(n+m)` worlds.

The count `3^n · 4^m` is exactly what an independent enumeration of the frames
produces (see `ComputationalEvidence.md`), and it exhibits the accessibility
relation as a *product* of `n` three-element button orders with `m` complete
two-element switch relations — the combinatorial form of the statement that buttons
and switches act independently.
-/

open MultiverseFrameCounting

open BooleanValuedRealization Finset

variable {α : Type*} [DecidableEq α]

theorem MultiverseFrameCounting.card_cacc_pairs(n m : ℕ) :
    ∑ v : CWorld (Fin n) (Fin m),
        (Finset.univ.filter fun w : CWorld (Fin n) (Fin m) => cacc w v).card
      = 3 ^ n * 4 ^ m := by sorry

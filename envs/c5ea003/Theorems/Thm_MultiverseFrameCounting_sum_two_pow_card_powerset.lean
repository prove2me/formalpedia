-- Prove2me | Theorems.Thm_MultiverseFrameCounting_sum_two_pow_card_powerset
-- name    : MultiverseFrameCounting.sum_two_pow_card_powerset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:38:31.882584+00:00
-- url     : https://prove2.me/theorems/38861fde-22ff-49ce-8adb-63ec5297af2b
-- title:
--   Enumerative lemma.
-- statement:
--   **Enumerative lemma.**  Summing `2^{|t|}` over all subsets `t` of `s` gives
--   `3^{|s|}`: each element of `s` contributes three states (absent, present only in
--   the ambient set, present in both).
--
--   ```lean
--   theorem MultiverseFrameCounting.sum_two_pow_card_powerset(s : Finset α) :
--       ∑ t ∈ s.powerset, 2 ^ t.card = 3 ^ s.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/FrameCounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/FrameCounting.lean#L33

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

theorem MultiverseFrameCounting.sum_two_pow_card_powerset(s : Finset α) :
    ∑ t ∈ s.powerset, 2 ^ t.card = 3 ^ s.card := by sorry

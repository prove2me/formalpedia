-- Prove2me | Definitions.Def_Logic_Multiverse_FrameCounting
-- name    : Logic_Multiverse_FrameCounting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:58:32.32781+00:00
-- url     : https://prove2.me/theorems/8432e3e7-ad59-4187-983a-4bfbd29e8bac
-- title:
--   Aether Catalog definitions — Logic_Multiverse_FrameCounting
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Multiverse.FrameCounting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Multiverse/FrameCounting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
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

namespace MultiverseFrameCounting

open BooleanValuedRealization Finset

variable {α : Type*} [DecidableEq α]

instance decidableCacc {Btn Sw : Type*} [DecidableEq Btn] :
    DecidableRel (cacc (Btn := Btn) (Sw := Sw)) :=
  fun w v => inferInstanceAs (Decidable (w.1 ⊆ v.1))





end MultiverseFrameCounting



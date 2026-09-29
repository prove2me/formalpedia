-- Prove2me | Theorems.Thm_AlmostLossless_exists_scanScheme_of_code
-- name    : AlmostLossless.exists_scanScheme_of_code
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:29.013379+00:00
-- url     : https://prove2.me/theorems/c29c7a37-7a33-4b84-ad78-c31bf1fcb6ed
-- title:
--   Honesty is free.
-- statement:
--   **Honesty is free.**  Every code `K` — honest or not — is matched, on its
--   correct set, by a uniqueness-scan code: the scan code is honest for free, has
--   exactly the same correct set, and its decoder probes at most one candidate.  The
--   only cost is the single extra alphabet symbol of `Option C`.
--
--   ```lean
--   theorem AlmostLossless.exists_scanScheme_of_code[DecidableEq C] (K : Code S C) :
--       ∃ P : ScanScheme S Unit C,
--         (∀ s : S, Correct (P.code ()) s ↔ Correct K s) ∧
--         Honest (P.code ()) ∧
--         (∀ m : C, P.decodeCost () m ≤ 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Optimality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Optimality.lean#L74

-- Thm stub generated from Logic/AlmostLossless/Optimality.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme

/-!
# Optimality: randomness is never useful, and honesty is free

Two structural results that close the loop opened by `Core` and `Scheme`.

* `AlmostLossless.randomized_epsilon_pigeonhole` — the exact `ε`-pigeonhole
  characterisation survives randomisation: if *any* randomized ensemble of codes
  has average failure probability `≤ ε`, then already a set of `≤ |C|` source
  words carries probability `≥ 1 - ε`, so a *deterministic* code achieves the
  same `ε`.  Shared randomness buys nothing, for **every** source (the earlier
  `randomized_avg_failProb_lower` was the uniform-source special case).

* `AlmostLossless.exists_scanScheme_of_code` — conversely, *every* code, honest
  or not, is matched on its correct set by a uniqueness-scan code, whose decoder
  probes at most **one** candidate.  So the "no silent corruption" guarantee
  costs one extra alphabet symbol and nothing else: no checksum, no rate loss
  beyond `+1`, no decoding time.
-/

open AlmostLossless

open Finset

variable {S C : Type*} [Fintype S] [DecidableEq S]

/-! ## Randomness never helps -/




/-! ## Honesty is free -/

theorem AlmostLossless.exists_scanScheme_of_code[DecidableEq C] (K : Code S C) :
    ∃ P : ScanScheme S Unit C,
      (∀ s : S, Correct (P.code ()) s ↔ Correct K s) ∧
      Honest (P.code ()) ∧
      (∀ m : C, P.decodeCost () m ≤ 1) := by sorry

-- Prove2me | Theorems.Thm_StrangeLoop_Girth_succ_loop_dvd
-- name    : StrangeLoop.Girth.succ_loop_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:37:22.641563+00:00
-- url     : https://prove2.me/theorems/e60bd13f-1237-4606-a753-ddf8fcee9f5d
-- title:
--   Every closed loop has length divisible by `n`.
-- statement:
--   **Every closed loop has length divisible by `n`.**  Traversing a closed
--   walk of the successor relation advances the index by the loop length and must
--   return to the start, forcing `n ∣ k`.
--
--   ```lean
--   theorem StrangeLoop.Girth.succ_loop_dvd{n k : ℕ} (v : ℕ → ZMod n)
--       (h : IsLoopN (succR n) k v) : n ∣ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/StrangeLoopGirth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/StrangeLoopGirth.lean#L73

-- Thm stub generated from Novelty/StrangeLoopGirth.lean
import Mathlib
import Definitions.Def_Novelty_StrangeLoopGirth
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# I Am a Strange Loop, Part VI: The Girth of a Tangled Hierarchy

Part II showed that an oriented (asymmetric) hierarchy admits no strange loop of
length `1` or `2`, while genuine loops appear at length `3` — the minimum
"strange-loop length".  Here we go deeper and compute the loop length exactly for
a tunable family of hierarchies, exhibiting *girth* as a controllable resource.

We study the cyclic **successor** relation `a ↦ a + 1` on `ZMod n`, the
prototypical tangled hierarchy (rock-paper-scissors when `n = 3`).  A closed walk
of length `k` in this relation forces the running index to advance by `k` and
return to its start, which is possible exactly when `n ∣ k`.  Consequently:

* a strange loop of length `n` always exists (`succ_loop_exists`);
* every closed loop has length divisible by `n` (`succ_loop_dvd`);
* hence the **minimum strange-loop length ("girth") is exactly `n`**
  (`succ_min_loop_length`).

This bridges the **combinatorics of tangled hierarchies** with the **arithmetic
of cyclic groups**: the depth of self-reference realizable in a hierarchy is
governed by a divisibility condition, and can be tuned to any prescribed value
`n ≥ 3`.  The generic bound "girth ≥ 3" of Part II becomes the exact identity
"girth = n" for these relations.

This file is fully self-contained.
-/

open StrangeLoop.Girth

open Relation

/-! ## Closed loops indexed by natural numbers with wraparound -/


/-! ## The successor relation on `ZMod n` -/

theorem StrangeLoop.Girth.succ_loop_dvd{n k : ℕ} (v : ℕ → ZMod n)
    (h : IsLoopN (succR n) k v) : n ∣ k := by sorry

-- Prove2me | Theorems.Thm_MagnitudeMirror_fermat_hit_index_bound
-- name    : MagnitudeMirror.fermat_hit_index_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:21:37.286346+00:00
-- url     : https://prove2.me/theorems/33af067a-e84c-40a1-b5d9-80c4557b7ebc
-- title:
--   Fermat frontier ascent law.
-- statement:
--   **Fermat frontier ascent law.**  For `N = u(u+2k)` with anchor `m = ⌊√N⌋`,
--   the offset `j = (u+k) − m` of the square-hit from the isqrt anchor satisfies
--   `2·m·j ≤ k² + 2·m`.  The distance from the anchor to the *hit* is controlled by
--   the factor imbalance `k`, not by any divisor position — this is the geometry the
--   retracted sign-change mechanism was mistaking for a channel.
--
--   ```lean
--   theorem MagnitudeMirror.fermat_hit_index_bound(u k : ℕ) :
--       2 * Nat.sqrt (u * (u + 2 * k)) * ((u + k) - Nat.sqrt (u * (u + 2 * k)))
--         ≤ k ^ 2 + 2 * Nat.sqrt (u * (u + 2 * k)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/MagnitudeMirrorTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/MagnitudeMirrorTransfer.lean#L178

-- Thm stub generated from Combinatorics/MagnitudeMirrorTransfer.lean
import Mathlib
import Definitions.Def_Combinatorics_MagnitudeMirrorSeal
/-
# Round-70 #6, cycle 2 — transfer beyond the magnitude: an exact characterisation
# of mirrors, the correct null, and the Fermat frontier cost law

Cycle 1 (`Combinatorics.MagnitudeMirrorSeal`) established that the realized
probes of papers 193/195 are structural constants or deterministic functions of
`N`'s magnitude, and that a magnitude mirror collapses to *exactly* zero
information inside every magnitude cell.  Cycle 2 asks the three questions the
critic raised against that synthesis.

1. **Is the collapse a characterisation, or only a consequence?**  It is a
   characterisation.  `zeroInfo_self_iff_const` shows that a statistic which is
   uninformative *about itself* is constant, and
   `mirror_iff_conditional_zeroInfo` upgrades this to: a feature collapses to
   exactly zero information inside every magnitude cell, against *every* secret,
   **iff** it is a deterministic function of the magnitude.  So "exact null given
   `|N|`" is not evidence-of-absence — it is *equivalent* to being a mirror.

2. **Why then did the row-shuffle null flag the mirror?**  Because a shuffle
   null tests the wrong hypothesis.  `zeroInfo_of_conditional_homogeneous` proves
   the exact converse direction: a mirror is *unconditionally* uninformative as
   soon as the secret's marginal is homogeneous across magnitude cells.  Hence
   `mirror_signal_forces_stratification`: if a mirror shows any unconditional
   signal at all, the secret's marginal provably varies across magnitude cells.
   Apparent signal from a deterministic function of `N` is scale stratification —
   a theorem, not a heuristic.

3. **What is the surviving geometry worth quantitatively?**  The Fermat frontier.
   `fermat_hit_index_bound` gives the exact ascent law
   `2·⌊√N⌋·j ≤ k² + 2·⌊√N⌋` for the offset `j` of the square-hit of
   `N = u(u+2k)` from the isqrt anchor, and `fermat_hit_index_le` turns it into
   the cost bound `j ≤ k²/(2⌊√N⌋) + 1`: the frontier distance is governed by the
   factor *imbalance* `k = (v−u)/2`, exactly the quantity the positional oracle
   `1{d ≤ B}` reads and no realized probe does.  Finally
   `oracle_capacity_superlevel_interval` shows the capacity profile of that
   oracle has interval superlevel sets, so the reported "`B*` for ≥90% of peak"
   is a well-defined threshold, not an artifact of the search grid.
-/

open MagnitudeMirror

open Finset Round11

variable {α : Type*} {β γ μ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq μ]

/-! ## 1. Zero self-information means constant -/


/-! ## 2. Mirrors are exactly the features with an exact conditional null -/


/-! ## 3. The correct null: conditional collapse plus homogeneous marginals -/



/-! ## 4. The Fermat frontier: an exact ascent law for the square-hit offset -/

theorem MagnitudeMirror.fermat_hit_index_bound(u k : ℕ) :
    2 * Nat.sqrt (u * (u + 2 * k)) * ((u + k) - Nat.sqrt (u * (u + 2 * k)))
      ≤ k ^ 2 + 2 * Nat.sqrt (u * (u + 2 * k)) := by sorry

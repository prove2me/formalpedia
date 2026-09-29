-- Prove2me | Theorems.Thm_MagnitudeMirror_mirror_iff_conditional_zeroInfo
-- name    : MagnitudeMirror.mirror_iff_conditional_zeroInfo
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:22:09.376399+00:00
-- url     : https://prove2.me/theorems/16c750be-8a16-44a6-b442-94c46e4722e5
-- title:
--   Characterisation of magnitude mirrors.
-- statement:
--   **Characterisation of magnitude mirrors.**  A feature has *exactly* zero
--   information about every secret inside every magnitude cell **iff** it is a
--   deterministic function of the magnitude.  So the exp551 measurement
--   "0.0000 bits given the magnitude decile, sd 0" is not weak evidence of no
--   channel: it is logically equivalent to the feature being a mirror.
--
--   ```lean
--   theorem MagnitudeMirror.mirror_iff_conditional_zeroInfo{Ω : Finset α} {Φ : α → β} {M : α → μ}
--       (hΩ : Ω.Nonempty) :
--       (∀ S : α → β, ∀ c : μ, ZeroInfo (Ω.filter fun w => M w = c) Φ S)
--         ↔ MirrorsMagnitude Ω Φ M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/MagnitudeMirrorTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/MagnitudeMirrorTransfer.lean#L77

-- Thm stub generated from Combinatorics/MagnitudeMirrorTransfer.lean
import Mathlib
import Definitions.Def_Combinatorics_MagnitudeMirrorSeal
import Definitions.Def_Combinatorics_Round11FingerprintInformation
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

theorem MagnitudeMirror.mirror_iff_conditional_zeroInfo{Ω : Finset α} {Φ : α → β} {M : α → μ}
    (hΩ : Ω.Nonempty) :
    (∀ S : α → β, ∀ c : μ, ZeroInfo (Ω.filter fun w => M w = c) Φ S)
      ↔ MirrorsMagnitude Ω Φ M := by sorry

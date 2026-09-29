-- Prove2me | Theorems.Thm_MagnitudeMirror_zeroInfo_of_conditional_homogeneous
-- name    : MagnitudeMirror.zeroInfo_of_conditional_homogeneous
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:22:41.607866+00:00
-- url     : https://prove2.me/theorems/594325ac-ba64-4b05-9502-93e367894ce5
-- title:
--   **A mirror is unconditionally uninformative once the secret is homogeneous
-- statement:
--   **A mirror is unconditionally uninformative once the secret is homogeneous
--   across magnitude cells.**  The hypothesis `hhom` says every magnitude cell has
--   the same empirical distribution of the secret (written multiplicatively, so no
--   division is needed).  Under it, a deterministic function of the magnitude has
--   exactly product fibre counts against the secret.
--
--   ```lean
--   theorem MagnitudeMirror.zeroInfo_of_conditional_homogeneous{Ω : Finset α} {Φ : α → β} {M : α → μ} {S : α → γ}
--       (hmir : MirrorsMagnitude Ω Φ M)
--       (hhom : ∀ c ∈ Ω.image M, ∀ s : γ,
--         #((Ω.filter fun w => M w = c).filter fun w => S w = s) * #Ω
--           = #(Ω.filter fun w => M w = c) * #(Ω.filter fun w => S w = s)) :
--       ZeroInfo Ω Φ S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/MagnitudeMirrorTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/MagnitudeMirrorTransfer.lean#L103

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


/-! ## 3. The correct null: conditional collapse plus homogeneous marginals -/

theorem MagnitudeMirror.zeroInfo_of_conditional_homogeneous{Ω : Finset α} {Φ : α → β} {M : α → μ} {S : α → γ}
    (hmir : MirrorsMagnitude Ω Φ M)
    (hhom : ∀ c ∈ Ω.image M, ∀ s : γ,
      #((Ω.filter fun w => M w = c).filter fun w => S w = s) * #Ω
        = #(Ω.filter fun w => M w = c) * #(Ω.filter fun w => S w = s)) :
    ZeroInfo Ω Φ S := by sorry

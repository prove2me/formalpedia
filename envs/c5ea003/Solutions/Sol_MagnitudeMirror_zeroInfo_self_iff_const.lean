-- Prove2me | solution 1 for MagnitudeMirror.zeroInfo_self_iff_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:58:15.520038+00:00
-- url     : https://prove2.me/submissions/8c3bda7c-117e-4a9f-b3e7-1b4ac5b6b709

-- Sol generated from Combinatorics/MagnitudeMirrorTransfer.lean
import Mathlib
import Definitions.Def_Combinatorics_MagnitudeMirrorSeal
import Definitions.Def_Combinatorics_Round11FingerprintInformation
import Theorems.Thm_Round11_zeroInfo_of_const
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




/-! ## 5. The oracle capacity profile has interval superlevel sets -/



/-! ## 6. Cycle 4: the frontier law is two-sided, and the capacity peak is exact
balance -/





open MagnitudeMirror in
theorem solution{Ω : Finset α} {T : α → β} (hΩ : Ω.Nonempty) :
    ZeroInfo Ω T T ↔ ∃ t₀, ∀ w ∈ Ω, T w = t₀ := by
  classical
  constructor
  · intro h
    obtain ⟨w₀, hw₀⟩ := hΩ
    refine ⟨T w₀, ?_⟩
    have hself : Ω.filter (fun w => T w = T w₀ ∧ T w = T w₀) = Ω.filter (fun w => T w = T w₀) :=
      Finset.filter_congr (fun w _ => by tauto)
    have h0 := h (T w₀) (T w₀)
    rw [hself] at h0
    have hpos : 0 < #(Ω.filter fun w => T w = T w₀) :=
      Finset.card_pos.2 ⟨w₀, Finset.mem_filter.2 ⟨hw₀, rfl⟩⟩
    have hcard : #(Ω.filter fun w => T w = T w₀) = #Ω := by
      have := h0
      nlinarith [this, hpos]
    have hsub : Ω.filter (fun w => T w = T w₀) = Ω :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq hcard.symm)
    intro w hw
    have : w ∈ Ω.filter (fun w => T w = T w₀) := by rw [hsub]; exact hw
    exact (Finset.mem_filter.1 this).2
  · rintro ⟨t₀, ht⟩
    exact zeroInfo_of_const ht

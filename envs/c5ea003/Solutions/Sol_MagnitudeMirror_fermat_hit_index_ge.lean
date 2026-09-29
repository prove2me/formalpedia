-- Prove2me | solution 1 for MagnitudeMirror.fermat_hit_index_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:54:58.219919+00:00
-- url     : https://prove2.me/submissions/024ab18e-54a1-416a-b714-6e7ef97df0b7

-- Sol generated from Combinatorics/MagnitudeMirrorTransfer.lean
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

/-- `⌊√N⌋` never exceeds the Fermat centre `u + k` of `N = u(u+2k)`. -/
theorem anchor_le_center (u k : ℕ) : Nat.sqrt (u * (u + 2 * k)) ≤ u + k := by
  have h : u * (u + 2 * k) ≤ (u + k) * (u + k) := by nlinarith
  calc Nat.sqrt (u * (u + 2 * k)) ≤ Nat.sqrt ((u + k) * (u + k)) := Nat.sqrt_le_sqrt h
  _ = u + k := Nat.sqrt_eq (u + k)



/-! ## 5. The oracle capacity profile has interval superlevel sets -/



/-! ## 6. Cycle 4: the frontier law is two-sided, and the capacity peak is exact
balance -/





theorem solution(u k : ℕ) :
    k ^ 2 ≤ 2 * (u + k) * ((u + k) - Nat.sqrt (u * (u + 2 * k))) := by
  set N := u * (u + 2 * k) with hN
  set m := Nat.sqrt N with hm
  have hma : m ≤ u + k := anchor_le_center u k
  obtain ⟨j, hj⟩ : ∃ j, u + k = m + j := ⟨(u + k) - m, by omega⟩
  have hjeq : (u + k) - m = j := by omega
  rw [hjeq]
  have hlow : m * m ≤ N := Nat.sqrt_le N
  have hsq : (m + j) * (m + j) = N + k * k := by
    rw [← hj, hN]; ring
  have hjm : m ≤ m + j := Nat.le_add_right _ _
  nlinarith [hlow, hsq, hjm, hj]

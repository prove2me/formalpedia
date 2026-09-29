-- Prove2me | solution 1 for ReorderL7Cap.card_coprime_class
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:55:02.146179+00:00
-- url     : https://prove2.me/submissions/50493942-18f5-41ac-bad5-c384745f5f5a

-- Sol generated from Novelty/ReorderMasterCapWitnesses.lean
import Mathlib
import Definitions.Def_Novelty_ReorderMasterCapWitnesses
/-
# GAP-L7' : the corrected master cap, its wheel calibration, and the two witness
# corrections

Companion to `Novelty.ReorderExtremalitySignFlip`.  That file falsified the
"√N-descending is extremal" clause of GAP-L7 and replaced it by a population
sign-flip law.  This file formalises the rest of the round-76 deliverable:

1. **The corrected master inequality L7'**
   `S ≤ (4/3) · min (1/μ_eff) 2^k / Λ`
   derived from touch-floor accounting plus the residue slack `4/3`
   (`speedup_le_capL7`), together with a *finite audit* of the reported
   measurement table (`audit_zero_violations`) and the two structural caveats:
   * `pure_permutation_cap_const` — booking `μ = 1` makes the cap a constant,
     i.e. tautological on pure-permutation cells;
   * `hybrid_cap_nonvacuous` — on the hybrid window×wheel cell the reported
     speedup `4.06` *exceeds* the cap computed with `μ` booked at `1`, and is
     comfortably under the cap computed with the structural keep fraction
     `μ = φ(30)/30`.  So the structural extraction of `μ_eff` (ledger item
     L7-d) is load-bearing, not cosmetic.
2. **Wheel calibration** (`wheel_keep_fraction`, `wheel_cap_eq`,
   `wheel_measured_under_cap`, `wheel_gap_bracket`): the mod-30 wheel keeps
   `φ(30)/30 = 4/15` of the candidates, so the protocol-A T1 law predicts
   `30/φ(30) = 15/4 = 3.75`; the measured headline `3.741` sits under the cap
   with a relative gap between `0.24%` and `0.31%`.
3. **Witness correction 1 — the Jacobi witness is retracted**
   (`jacobi_witness_degenerate`, `jacobi_witness_constant`,
   `jacobi_nonzero_of_coprime`): for `N = p·q` the Jacobi symbol `(N | p)`
   vanishes *identically*, because `p ∣ N`.  The statistic is constant across
   the whole draw space, hence carries zero bits; it measures algebraic
   degeneracy ("`p` divides `N`"), not prior shape.
4. **Witness correction 2 — the keyed-vs-fixed mod-3 control**
   (`card_residue_class`, `keyed_vs_fixed_mod3_identical`,
   `mod3_promotion_factor_blind`): a promotion rule that selects one invertible
   residue class mod 3 promotes exactly half of the candidates coprime to 3,
   *whatever* the key is — in particular an `N`-keyed rule and a fixed-key rule
   are statistically identical.  Residue couplings carry zero information; any
   apparent gain is prior-shape leakage.

-- !-- Lab Notes -- !--
-- Audit cells below are the reported round-74/76 verification numbers:
-- wheel arm 3.7331 / 3.741 / 3.7496 against the 15/4 = 3.75 law (gap 0.25-0.31%);
-- keyed vs fixed mod-3 promotion S = 0.6366 / 0.6537 (BAL_prime) and
-- 0.684 / 0.660 (P137); narrow-band win_asc S = 0.5682; paper-137 trunc_asc
-- S = 0.9278 (asc/desc = 1.078x); ladder-aligned S = 0.990, ladder-naive 0.27;
-- hybrid window x wheel on P137, S = 4.06 at Lambda = 0.7533.
-- `audit_zero_violations` checks every one of them against the L7' cap: no
-- violations.
-/

open ReorderL7Cap

open Finset

/-! ## 1.  The corrected master inequality -/



/-! ### The finite audit of the reported measurement table -/






/-! ## 2.  Wheel calibration against the protocol-A T1 law -/





/-! ## 3.  Witness correction 1 : the Jacobi witness is algebraically degenerate -/




/-! ## 4.  Witness correction 2 : the keyed-vs-fixed mod-3 control -/

/-- Each residue class mod `3` holds exactly `m` of the first `3m` candidates. -/
theorem card_residue_class (m c : ℕ) (hc : c < 3) :
    ({x ∈ Finset.range (3 * m) | x % 3 = c}).card = m := by
  classical
  have : ({x ∈ Finset.range (3 * m) | x % 3 = c}).card = (Finset.range m).card := by
    refine Finset.card_bij' (fun x _ => x / 3) (fun i _ => 3 * i + c) ?_ ?_ ?_ ?_ <;>
      intro x hx <;> simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢ <;> omega
  simpa using this





open ReorderL7Cap in
theorem solution(m : ℕ) :
    ({x ∈ Finset.range (3 * m) | x % 3 ≠ 0}).card = 2 * m := by
  classical
  have hsplit : ({x ∈ Finset.range (3 * m) | x % 3 ≠ 0}).card
      = ({x ∈ Finset.range (3 * m) | x % 3 = 1}).card
        + ({x ∈ Finset.range (3 * m) | x % 3 = 2}).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
      omega
    · refine Finset.disjoint_filter.mpr ?_
      intro x _ h1 h2
      omega
  rw [hsplit, card_residue_class m 1 (by norm_num), card_residue_class m 2 (by norm_num)]
  ring

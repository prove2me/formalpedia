-- Prove2me | Theorems.Thm_ReorderL7Cap_speedup_le_capL7
-- name    : ReorderL7Cap.speedup_le_capL7
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:28:35.442922+00:00
-- url     : https://prove2.me/theorems/4b227d8d-5429-40cf-9412-117c641becbd
-- title:
--   Master inequality L7' (real form).
-- statement:
--   **Master inequality L7' (real form).**  `Cdesc/CA ≤ (4/3)·min(1/μ)·2^k / Λ`.
--
--   The two hypotheses are the two accounting floors: the *touch floor*
--   `Λ·μ·Cdesc ≤ (4/3)·CA` (the algorithm must still touch a `μ`-fraction of the
--   index set, up to the residue slack `4/3`), and the *bit floor*
--   `Λ·Cdesc ≤ (4/3)·2^k·CA` (a `k`-bit filter cannot separate more than `2^k`
--   buckets).  Neither uses uniformity inside cells.
--
--   ```lean
--   theorem ReorderL7Cap.speedup_le_capL7{Cdesc CA muEff lam twok : ℝ}
--       (hCA : 0 < CA) (hmu : 0 < muEff) (hlam : 0 < lam)
--       (htouch : lam * muEff * Cdesc ≤ (4 / 3) * CA)
--       (hbits : lam * Cdesc ≤ (4 / 3) * twok * CA) :
--       Cdesc / CA ≤ (4 / 3) * min (1 / muEff) twok / lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReorderMasterCapWitnesses.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReorderMasterCapWitnesses.lean#L60

-- Thm stub generated from Novelty/ReorderMasterCapWitnesses.lean
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

theorem ReorderL7Cap.speedup_le_capL7{Cdesc CA muEff lam twok : ℝ}
    (hCA : 0 < CA) (hmu : 0 < muEff) (hlam : 0 < lam)
    (htouch : lam * muEff * Cdesc ≤ (4 / 3) * CA)
    (hbits : lam * Cdesc ≤ (4 / 3) * twok * CA) :
    Cdesc / CA ≤ (4 / 3) * min (1 / muEff) twok / lam := by sorry

-- Prove2me | Definitions.Def_Novelty_ReorderMasterCapWitnesses
-- name    : Novelty_ReorderMasterCapWitnesses
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:56.44538+00:00
-- url     : https://prove2.me/theorems/d8434117-1516-4303-86f6-7e02efdc5ed0
-- title:
--   Aether Catalog definitions — Novelty_ReorderMasterCapWitnesses
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ReorderMasterCapWitnesses`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ReorderMasterCapWitnesses.lean by skeleton subtraction
import Mathlib
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

namespace ReorderL7Cap

open Finset

/-! ## 1.  The corrected master inequality -/

/-- The L7' cap `(4/3) · min (1/μ_eff) 2^k / Λ`. -/
def capL7 (muEff twok lam : ℚ) : ℚ := (4 / 3) * min (1 / muEff) twok / lam


/-! ### The finite audit of the reported measurement table -/

/-- One measured cell of the verification table: reported speedup `S`, booked
structural keep-fraction `mu`, bit budget `twok = 2^k`, prior-shape factor
`lam = Λ`. -/
structure AuditCell where
  S : ℚ
  mu : ℚ
  twok : ℚ
  lam : ℚ
deriving DecidableEq

/-- The reported round-74/76 verification table (four pools, all policy arms). -/
def auditTable : List AuditCell :=
  [ -- wheel arm, protocol-A T1 law
    ⟨3.7331, 4/15, 32, 1⟩, ⟨3.741, 4/15, 32, 1⟩, ⟨3.7496, 4/15, 32, 1⟩,
    -- keyed vs fixed mod-3 promotion, BAL_prime and P137
    ⟨0.6366, 1, 32, 1⟩, ⟨0.6537, 1, 32, 1⟩, ⟨0.684, 1, 32, 1⟩, ⟨0.660, 1, 32, 1⟩,
    -- narrow-band window arms
    ⟨0.5682, 1, 32, 1⟩, ⟨1, 1, 32, 1⟩,
    -- paper-137 pool: truncated ascending against descending
    ⟨0.9278, 1, 32, 1⟩,
    -- exp570 ladder surrogates
    ⟨0.990, 1, 32, 1⟩, ⟨0.27, 1, 32, 1⟩,
    -- hybrid window x wheel stress arm on P137
    ⟨4.06, 4/15, 32, 0.7533⟩ ]




/-! ## 2.  Wheel calibration against the protocol-A T1 law -/





/-! ## 3.  Witness correction 1 : the Jacobi witness is algebraically degenerate -/




/-! ## 4.  Witness correction 2 : the keyed-vs-fixed mod-3 control -/





end ReorderL7Cap



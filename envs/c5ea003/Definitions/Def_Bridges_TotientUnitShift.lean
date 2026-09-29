-- Prove2me | Definitions.Def_Bridges_TotientUnitShift
-- name    : Bridges_TotientUnitShift
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:58.016174+00:00
-- url     : https://prove2.me/theorems/d519d956-e9b7-49a1-af35-bf3fd632b731
-- title:
--   Aether Catalog definitions — Bridges_TotientUnitShift
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TotientUnitShift`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TotientUnitShift.lean by skeleton subtraction
import Mathlib
/-
# Tightness of the unit-shift bound for Euler's totient function

The deep analytic theorem of Graham, Holt and Pomerance asserts that the counting
function of unit-shift totient collisions,

  S₁^φ(x) = #{ n ≤ x : φ(n) = φ(n+1) },

satisfies a lower bound matching the upper bound
`S₁^φ(x) ≪ x·exp{-(1/2 - o(1))·√(log x · log₂ x)}`; that is, the bound is *tight*.
A full formalization of the asymptotic is out of reach, but its logical skeleton
is not: the lower bound is proved by *constructing* many `n` with φ(n)=φ(n+1) and
*counting* them.  This file formalizes that skeleton.

We
* define `S1phi`, the unit-shift collision counting function;
* prove it is monotone and never saturates (`S1phi x < x` for `x ≥ 2`);
* prove the **counting transfer theorem** `S1phi_ge_card`: any finite set of
  certified witnesses gives a lower bound on `S1phi` — the formal core of the
  GHP lower-bound strategy;
* deduce explicit unconditional lower bounds `6 ≤ S1phi 194` and `10 ≤ S1phi 975`
  from the multiplicatively-verified witnesses in `TotientShiftWitnesses.lean`;
* prove a structural constraint: every unit-shift collision value (for `n ≥ 3`)
  is even.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):
  H1 (bold): S₁^φ(x) → ∞.  [Infinitude of φ(n)=φ(n+1) — OPEN; not claimed here.]
  H2: The lower bound on S₁^φ is obtained constructively; a verified set of
      witnesses below x is a verified lower bound on S₁^φ(x).
  H3: Collision values are constrained (parity), ruling out trivial saturation.

Experiment (Experimenter):
  - Computed all witnesses ≤ 1000: {1,3,15,104,164,194,255,495,584,975} (10 of them).
  - Formalized the transfer theorem `S1phi_ge_card` (H2): proved by exhibiting the
    witness set as a subset of the filtered interval (`Finset.card_le_card`).
  - For H3 used `Nat.totient_even`.
  - For non-saturation, exhibited `2` as a certified non-collision
    (φ(2)=1 ≠ 2=φ(3)), giving a strict subset.

Analysis (Analyst):
  - H2 is "true and clean": it isolates exactly what the GHP construction must
    supply (witnesses) from the bookkeeping (counting).  SURVIVED.
  - H3 SURVIVED and explains why the trivial upper bound S₁^φ(x) ≤ x is never
    attained: collisions are sparse already for parity reasons at the top.
  - H1 remains OPEN: no infinite certified family is known elementarily; the GHP
    machinery is genuinely analytic.  This is the true mathematical frontier.

Critique (Critic):
  - `S1phi_ge_card` is not vacuous: its hypotheses are met by real witnesses and
    used to derive a nontrivial `10 ≤ S1phi 975`.
  - No main theorem is a bare `decide`/`native_decide`; the explicit bounds route
    through the transfer theorem and the multiplicative witnesses.
  - `totient_shift_value_even` uses the hypothesis genuinely (rewrites along the
    collision and applies `Nat.totient_even`).

Synthesis (PI): The constructive lower-bound skeleton for the tightness statement
is fully formalized and unconditional at every finite stage; the only missing
ingredient for the full theorem is the (open/analytic) production of a dense
infinite family — recorded in FUTURE_DIRECTIONS.md.
-/

open Nat Finset

set_option maxRecDepth 100000

namespace TotientShift

/-- `S1phi x` counts the integers `n` with `1 ≤ n ≤ x` satisfying the unit-shift
totient collision `φ(n) = φ(n+1)`.  This is the function written `S₁^φ(x)` in the
Graham–Holt–Pomerance work. -/
noncomputable def S1phi (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => Nat.totient n = Nat.totient (n + 1))).card








end TotientShift



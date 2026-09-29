-- Prove2me | Theorems.Thm_TotientShift_S1phi_lt_self
-- name    : TotientShift.S1phi_lt_self
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:17:27.03033+00:00
-- url     : https://prove2.me/theorems/d842e5d8-d76c-4f69-b050-89bb9c3e86fd
-- title:
--   Non-saturation: for `x ≥ 2` strictly fewer than `x` integers collide, since
-- statement:
--   Non-saturation: for `x ≥ 2` strictly fewer than `x` integers collide, since
--   `n = 2` is a certified non-collision (`φ(2) = 1 ≠ 2 = φ(3)`).  Thus the trivial
--   upper bound is never attained.
--
--   ```lean
--   theorem TotientShift.S1phi_lt_self{x : ℕ} (hx : 2 ≤ x) : S1phi x < x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GameTheory/TotientUnitShift.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GameTheory/TotientUnitShift.lean#L157

-- Thm stub generated from Bridges/TotientUnitShift.lean
import Mathlib
import Definitions.Def_Bridges_TotientUnitShift
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

open TotientShift

theorem TotientShift.S1phi_lt_self{x : ℕ} (hx : 2 ≤ x) : S1phi x < x := by sorry

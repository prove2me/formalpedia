-- Prove2me | solution 1 for MomentHierarchy.orbitCount_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T07:31:40.332071+00:00
-- url     : https://prove2.me/submissions/de2ae705-bb25-418e-8384-c49a530d603f

/-
# `MomentHierarchy.orbitCount_le_succ`
Target `61576931` (Open; re-read live immediately before submitting).

ORDINARY PROOF — `scripts/screen_bundles.sh` returns CLEAN (exit 0).

BINDERS — expected type, verbatim from the WA:

    ∀ {G} {X} [Group G] [Fintype G] [MulAction G X] [Finite X] (k : ℕ),
      1 ≤ k → orbitCount G X k ≤ orbitCount G X (k + 1)

The hypothesis appears as an anonymous arrow; writing it as a named binder `(hk : 1 ≤ k)` elaborates
to the same ∀-type. Familiar family: [Fintype G] BEFORE [MulAction G X], [Finite X] once.

MATHS. Via the moment identity (owned as `34c897b0`, re-derived inline rather than imported, since
importing `Theorems.` would force the axiom-audit path):

    orbitCount G X j · |G| = ∑ g, |X^g| ^ j

so the claim reduces to `∑ g, |X^g|^k ≤ ∑ g, |X^g|^(k+1)`, which holds TERMWISE for every natural
base: at `|X^g| = 0` both sides are 0 — and this is exactly where `1 ≤ k` earns its place, since
`0^0 = 1` would break it — and at `|X^g| ≥ 1` it is monotonicity of powers. Cancelling the positive
`|G|` finishes.

PROBED, NOT GUESSED — each confirmed by CALL SITES in Mathlib (valid evidence: Mathlib compiles):
  * `Nat.pow_le_pow_right` — used as `Nat.pow_le_pow_right hn kw : n^k ≤ n^w`, base-positivity first.
  * `Finset.sum_le_sum` — used as `Finset.sum_le_sum fun i hi => ...`.
  * `Nat.le_of_mul_le_mul_right` — used as `Nat.le_of_mul_le_mul_right ?_ (0 < c)`.
  * No `Nat.le_self_pow` / `pow_le_pow_succ` exists, so the base is case-split explicitly.
  * `orbitCount` is a `def`, NOT an abbrev, so its boundary is crossed by `show` (definitional),
    never by rw/simp — the discipline that worked for `31e94748` and `1d20e30d`.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X]
    (k : ℕ) (hk : 1 ≤ k) :
    orbitCount G X k ≤ orbitCount G X (k + 1) := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ (j : ℕ) (g : G), Fintype (fixedBy (Fin j → X) g) := fun _ _ => Fintype.ofFinite _
  haveI : ∀ j : ℕ, Fintype (Quotient (orbitRel G (Fin j → X))) := fun _ => Fintype.ofFinite _
  -- the moment identity, re-derived inline at an arbitrary exponent
  have hmom : ∀ j : ℕ, orbitCount G X j * Nat.card G
      = ∑ g : G, Nat.card (fixedBy X g) ^ j := by
    intro j
    have hpow : ∀ g : G, Nat.card (fixedBy X g) ^ j = Nat.card (fixedBy (Fin j → X) g) := by
      intro g
      rw [Nat.card_congr (MomentHierarchy.fixedByPiEquiv g), Nat.card_fun, Nat.card_fin]
    have hburn : (∑ g : G, Nat.card (fixedBy (Fin j → X) g))
        = Nat.card (Quotient (orbitRel G (Fin j → X))) * Nat.card G := by
      simp only [Nat.card_eq_fintype_card]
      exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin j → X)
    show Nat.card (orbitRel.Quotient G (Fin j → X)) * Nat.card G = _
    exact hburn.symm.trans (Finset.sum_congr rfl (fun g _ => (hpow g).symm))
  -- termwise monotonicity of the summands
  have hterm : ∀ g : G, Nat.card (fixedBy X g) ^ k ≤ Nat.card (fixedBy X g) ^ (k + 1) := by
    intro g
    rcases Nat.eq_zero_or_pos (Nat.card (fixedBy X g)) with h | h
    · rw [h, zero_pow (by omega), zero_pow (by omega)]
    · exact Nat.pow_le_pow_right h (by omega)
  -- cancel the positive group order.
  -- BIND the positivity fact FIRST with an explicit type: inlined as the second argument, its `α`
  -- is only determined by the `?_` goal, which elaborates later, leaving `Finite ?m` stuck.
  have hGpos : 0 < Nat.card G := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hGpos
  rw [hmom k, hmom (k + 1)]
  exact Finset.sum_le_sum (fun g _ => hterm g)

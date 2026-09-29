-- Prove2me | solution 1 for MomentHierarchy.orbitCount_one_mul_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T07:55:36.832601+00:00
-- url     : https://prove2.me/submissions/c35deb73-1001-478f-b9e2-0824abf627ed

/-
# `MomentHierarchy.orbitCount_one_mul_le_succ`
Target `d91f67b6` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN (exit 0). Gift check: its graph contains ZERO sketches, so there is no
competitor position on this node at all.

BINDERS — this target has NO WA, so no rejection publishes an expected type. I first inferred them
from `section Hierarchy` and the GATE REJECTED IT: "solution has 7 binders". The MIRROR, generated
byte-identically from the API, shows the statement actually sits under

    variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nonempty X]

so `[Nonempty X]` IS declared — eight binders. My error was deducing from the CE messages that the
PROOF does not need `Nonempty X` (true) and concluding the STATEMENT does not declare it (false).
A hypothesis can be declared and unused. Where there is no WA, read the mirror, never infer the
section.

WHAT THE THREE CEs TELL ME. Every prior attempt failed with

    failed to synthesize instance of type class  Nonempty X

That is not a defect in the statement — it says the submitter's ROUTE needed a base point of `X`,
which the expected type does not provide. It holds without one: for empty `X`, `k = 0` reads
`0 * 1 ≤ 0` and `k ≥ 1` reads `0 * 0 ≤ 0`, both true. So any argument that picks a point of `X` is
the wrong argument, and this proof deliberately picks none.

MATHS. The note calls it "log-convexity integrated once". Through the moment identity
(owned as `34c897b0`, re-derived inline rather than imported so the closure stays definitions-only):

    orbitCount G X j · |G| = ∑ g, |X^g| ^ j  =: S j

Multiplying the goal by `|G|²` turns it into `S 1 · S k ≤ |G| · S (k+1)`, which is **Chebyshev's sum
inequality** for two monovarying sequences — NOT Cauchy-Schwarz, which is the neighbouring
log-convexity result.

PROBED, NOT GUESSED — read out of source:
  * `Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g)` (Chebyshev.lean:146), in the `Mul`
    section assuming `[Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]` — the
    SAME four that Cauchy-Schwarz needs, and `ℕ` satisfies all of them.
  * `monovary_self (f) : Monovary f f` (Monovary.lean:99)
  * `Monovary.pow_right (hfg) (n) : Monovary f (g ^ n)` (Algebra/Order/Monovary.lean:182)
  * COMPILE CORRECTION: `Monovary.pow_right` requires `[CommGroup β]` on the CODOMAIN of `g`.
    `ℕ` is not a group, so it does not apply — the probe caught this. The monovariance is proved
    directly instead, from `Nat.pow_le_pow_left` by contraposition. Chebyshev's inequality itself
    is unaffected and does apply over `ℕ`.
  * The conclusion carries `↑(Fintype.card ι)`; over `ℕ` that cast is `Nat.cast_id`.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nonempty X]
    (k : ℕ) :
    orbitCount G X 1 * orbitCount G X k ≤ orbitCount G X (k + 1) := by
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
  -- Chebyshev on the moment sequence: the two sequences monovary because one is a power of the other
  have hcheb : (∑ g : G, Nat.card (fixedBy X g) ^ 1) * (∑ g : G, Nat.card (fixedBy X g) ^ k)
      ≤ Nat.card G * ∑ g : G, Nat.card (fixedBy X g) ^ (k + 1) := by
    have hm : Monovary (fun g : G => Nat.card (fixedBy X g))
                       (fun g : G => Nat.card (fixedBy X g) ^ k) := by
      intro i j hij
      by_contra hcon
      push_neg at hcon
      exact absurd hij (not_lt.mpr (Nat.pow_le_pow_left hcon.le k))
    have h := hm.sum_mul_sum_le_card_mul_sum
    simpa [pow_one, pow_succ, Nat.card_eq_fintype_card, Nat.cast_id, mul_comm] using h
  -- cancel |G|², which is positive
  have hGpos : 0 < Nat.card G := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hGpos hGpos)
  calc orbitCount G X 1 * orbitCount G X k * (Nat.card G * Nat.card G)
      = (orbitCount G X 1 * Nat.card G) * (orbitCount G X k * Nat.card G) := by ring
    _ = (∑ g : G, Nat.card (fixedBy X g) ^ 1) * (∑ g : G, Nat.card (fixedBy X g) ^ k) := by
        rw [hmom 1, hmom k]
    _ ≤ Nat.card G * ∑ g : G, Nat.card (fixedBy X g) ^ (k + 1) := hcheb
    _ = Nat.card G * (orbitCount G X (k + 1) * Nat.card G) := by rw [hmom (k + 1)]
    _ = orbitCount G X (k + 1) * (Nat.card G * Nat.card G) := by ring

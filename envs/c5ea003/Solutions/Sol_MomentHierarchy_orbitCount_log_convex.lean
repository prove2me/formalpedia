-- Prove2me | solution 1 for MomentHierarchy.orbitCount_log_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T07:37:47.862647+00:00
-- url     : https://prove2.me/submissions/e6414890-909d-42db-a799-2558ff1e370f

/-
# `MomentHierarchy.orbitCount_log_convex`
Target `a82556da` (Open; re-read live immediately before submitting).

ORDINARY PROOF — same bundle as the other MomentHierarchy targets, screened CLEAN.

BINDERS — expected type, verbatim from the WA:

    ∀ {G} {X} [Group G] [Fintype G] [MulAction G X] [Finite X] (k : ℕ),
      orbitCount G X (k + 1) ^ 2 ≤ orbitCount G X k * orbitCount G X (k + 2)

No hypothesis on k. Familiar family: [Fintype G] BEFORE [MulAction G X], [Finite X] once.

MATHS. The orbit counts are, up to the factor |G|, the moments of the fixed-point statistic:

    orbitCount G X j · |G| = ∑ g, |X^g| ^ j

Log-convexity is then Cauchy-Schwarz on that sequence. Multiplying both sides by |G|² turns the goal
into `(∑ a^(k+1))² ≤ (∑ a^k)(∑ a^(k+2))`, which is Cauchy-Schwarz with
`r = a^(k+1)`, `f = a^k`, `g = a^(k+2)` — and its side condition `r² ≤ f · g` is an IDENTITY here,
since both sides are `a^(2k+2)`.

A CORRECTION I MADE TO MY OWN EARLIER ANALYSIS. I had deferred this target believing Mathlib's
Cauchy-Schwarz needed a `LinearOrderedCommRing`, so that a proof over `ℕ` would have to cast to `ℝ`
and back. That was WRONG — an old spelling, not this Mathlib's. The real requirement is
`[CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]`
(Algebra/Order/BigOperators/Ring/Finset.lean:159), all of which `ℕ` satisfies; Mathlib itself
instantiates it at `(R := ℕ)` in Combinatorics/Additive/Energy.lean:147. There is no cast layer.

PROBED, NOT GUESSED:
  * `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` (same file, :126) — takes non-negativity of `f` and
    `g` on the set and the pointwise bound `r i ^ 2 ≤ f i * g i`. Preferred over the squared form
    because our side condition is naturally stated that way.
  * `orbitCount` is a `def`, so its boundary is crossed by `show`/defeq, never by rw/simp.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] (k : ℕ) :
    orbitCount G X (k + 1) ^ 2 ≤ orbitCount G X k * orbitCount G X (k + 2) := by
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
  -- Cauchy-Schwarz on the moment sequence, directly over ℕ
  have hcs : (∑ g : G, Nat.card (fixedBy X g) ^ (k + 1)) ^ 2
      ≤ (∑ g : G, Nat.card (fixedBy X g) ^ k) * ∑ g : G, Nat.card (fixedBy X g) ^ (k + 2) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) ?_
    intro g _
    have h : (k + 1) * 2 = k + (k + 2) := by ring
    rw [← pow_mul, ← pow_add, h]
  -- cancel |G|², which is positive
  have hGpos : 0 < Nat.card G := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hGpos hGpos)
  calc orbitCount G X (k + 1) ^ 2 * (Nat.card G * Nat.card G)
      = (orbitCount G X (k + 1) * Nat.card G) ^ 2 := by ring
    _ = (∑ g : G, Nat.card (fixedBy X g) ^ (k + 1)) ^ 2 := by rw [hmom (k + 1)]
    _ ≤ (∑ g : G, Nat.card (fixedBy X g) ^ k) * ∑ g : G, Nat.card (fixedBy X g) ^ (k + 2) := hcs
    _ = (orbitCount G X k * Nat.card G) * (orbitCount G X (k + 2) * Nat.card G) := by
        rw [hmom k, hmom (k + 2)]
    _ = orbitCount G X k * orbitCount G X (k + 2) * (Nat.card G * Nat.card G) := by ring

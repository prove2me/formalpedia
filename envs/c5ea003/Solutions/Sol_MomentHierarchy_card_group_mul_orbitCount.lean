-- Prove2me | solution 1 for MomentHierarchy.card_group_mul_orbitCount
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T07:25:38.606292+00:00
-- url     : https://prove2.me/submissions/dc8d6681-e57c-4502-85d6-c651de8c7c8b

/-
# `MomentHierarchy.card_group_mul_orbitCount`
Target `31e94748-02e8-4817-a0db-b36cfb395e10` (Open; re-read live immediately before submitting).

ORDINARY PROOF — same preamble bundle as `34c897b0`, screened CLEAN.

BINDERS — expected type, verbatim from the WA (identical binders to `34c897b0`):

    ∀ {G} {X} [Group G] [Fintype G] [MulAction G X] [Finite X] (k : ℕ),
      MomentHierarchy.orbitCount G X k * Nat.card G = ∑ g, Nat.card ↑(fixedBy X g) ^ k

MATHS. This is `34c897b0` with the sides swapped and the abbreviation folded:
`orbitCount G X k` is DEFINED as `Nat.card (orbitRel.Quotient G (Fin k → X))`
(Def_Logic_MomentHierarchy.lean, section Hierarchy), so the two statements carry the same content.

THE ONE REAL DIFFERENCE, and it is the trap this session has hit twice already:
`orbitCount` is a **`noncomputable def`, NOT an `abbrev`**. `orbitRel.Quotient` IS an abbrev, which
is why `34c897b0` could cross that boundary silently. A `def` is only semi-reducible, so it will not
unfold on its own the way the abbrev did. The boundary is therefore crossed with `show`, which works
up to definitional unfolding, and NEVER with `rw`/`simp` — today's `Walk.mapLe` failure proved that
a reducible definition can be transparent to the elaborator and still opaque to `simp`.

Probe (A) below tests exactly that with `rfl`, so if this reasoning is wrong the compile says so in
one line rather than failing somewhere obscure.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] (k : ℕ) :
    orbitCount G X k * Nat.card G = ∑ g : G, Nat.card (fixedBy X g) ^ k := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ g : G, Fintype (fixedBy (Fin k → X) g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel G (Fin k → X))) := Fintype.ofFinite _
  have hpow : ∀ g : G, Nat.card (fixedBy X g) ^ k = Nat.card (fixedBy (Fin k → X) g) := by
    intro g
    rw [Nat.card_congr (MomentHierarchy.fixedByPiEquiv g), Nat.card_fun, Nat.card_fin]
  have hburn : (∑ g : G, Nat.card (fixedBy (Fin k → X) g))
      = Nat.card (Quotient (orbitRel G (Fin k → X))) * Nat.card G := by
    simp only [Nat.card_eq_fintype_card]
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin k → X)
  -- cross the `def` boundary by `show` (definitional), never by a rewrite
  show Nat.card (orbitRel.Quotient G (Fin k → X)) * Nat.card G = _
  calc Nat.card (orbitRel.Quotient G (Fin k → X)) * Nat.card G
      = ∑ g : G, Nat.card (fixedBy (Fin k → X) g) := hburn.symm
    _ = ∑ g : G, Nat.card (fixedBy X g) ^ k :=
        Finset.sum_congr rfl (fun g _ => (hpow g).symm)

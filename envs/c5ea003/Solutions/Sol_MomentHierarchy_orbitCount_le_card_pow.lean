-- Prove2me | solution 1 for MomentHierarchy.orbitCount_le_card_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:26:43.007357+00:00
-- url     : https://prove2.me/submissions/2cca9915-6b6d-4f12-97ff-be79be094d9d

/-
# `MomentHierarchy.orbitCount_le_card_pow`
Target `5a228a46` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`orbitCount G X k = Nat.card (orbitRel.Quotient G (Fin k → X))`. The quotient map out of
`Fin k → X` is surjective, so the quotient is no larger than the function type, and
`Nat.card (Fin k → X) = Nat.card X ^ k`.

BINDERS: copied verbatim from the platform's expected type. Note the ORDER —
  [Group G] [Fintype G] [MulAction G X] [Finite X]
with `Fintype G` BEFORE `MulAction G X`. Three prior submissions were rejected for supplying the
same four instances in a different order; instance binder order is part of the type.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false

open MomentHierarchy in
/-- **The target, verbatim.** -/
theorem solution {G : Type*} {X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] (k : ℕ) :
    orbitCount G X k ≤ Nat.card X ^ k := by
  classical
  have hfin : Finite (Fin k → X) := inferInstance
  have hcard : Nat.card (Fin k → X) = Nat.card X ^ k := by
    first
    | simp [Nat.card_fun]
    | simp [Nat.card_pi]
    | · rw [Nat.card_pi]
        simp
    | simp [Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective
      (Quotient.mk (MulAction.orbitRel G (Fin k → X))) := Quotient.mk_surjective
  calc orbitCount G X k
      = Nat.card (MulAction.orbitRel.Quotient G (Fin k → X)) := rfl
    _ ≤ Nat.card (Fin k → X) := by
        first
        | exact Nat.card_le_card_of_surjective _ hsurj
        | exact Nat.card_le_card_of_surjective (Quotient.mk _) Quotient.mk_surjective
        | exact Finite.card_le_of_surjective _ hsurj
    _ = Nat.card X ^ k := hcard

-- Prove2me | solution 1 for obs_iff_equiv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:20:46.999701+00:00
-- url     : https://prove2.me/submissions/1a9a5b91-01bc-4282-8157-ac592fedf168

-- Sol generated from Bridges/UltrametricProofCompressionDuality.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricProofCompressionDuality
/-
# Ultrametric Proof Compression Duality via Observer Semimodules and
  Certified Minimal Refutation Reconstruction

This file formalizes a **finite algebraic realization theorem** for proof compression.
The main theorem establishes a canonical bijection between extremal observer classes
and minimal automaton states, analogous to Myhill–Nerode for proof compression.

## Bridges

- Ultrametric geometry ↔ Proof compression dynamics
- Prime congruence algebra ↔ Automata minimization (Myhill–Nerode)
- Observer separation ↔ Certified refutation reconstruction
-/


open Function Finset Classical

noncomputable section

/-! ## §1. Ultrametric Foundations -/


/-! ## §2. Finite Compressed Proof System -/


variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## §3. Behavioral Equivalence (Myhill–Nerode style) -/










/-! ## §4. Minimal Compressed Refutation Automaton -/


attribute [instance] MinCompRefAut.instFin
attribute [instance] MinCompRefAut.instDE


/-! ## §5. Observer Semimodule -/


attribute [instance] ObsSemimod.instFin
attribute [instance] ObsSemimod.instDE










/-! ## §6. Core Lemmas -/













/-! ## §7. Extremal Ray–State Bijection -/


/-! ## §8. Helper: surjective maps with same kernel induce equiv on codomains -/

/-
If two surjective functions from P to finite types have the same kernel
(i.e. agree on which pairs map to the same element), their codomains are
in bijection.
-/

/-! ## §9. Uniqueness of Minimal Automaton -/


/-! ## §10. Main Duality Theorem -/


/-! ## §11. Reconstruction Converse -/








theorem solution(S : FinCompProofSys P) (x y : P) :
    (∀ c : (Obs S).Carrier, (Obs S).eval c x = (Obs S).eval c y) ↔
    behEquiv S x y := by
  constructor
  · intro h
    by_contra hne
    have hneq : @Quotient.mk _ (behSetoid S) y ≠ @Quotient.mk _ (behSetoid S) x :=
      fun heq => hne (behEquiv_symm S (Quotient.exact heq))
    specialize h (@Quotient.mk _ (behSetoid S) x)
    change (if @Quotient.mk _ (behSetoid S) x = @Quotient.mk _ (behSetoid S) x then 1 else 0) =
           (if @Quotient.mk _ (behSetoid S) y = @Quotient.mk _ (behSetoid S) x then 1 else 0) at h
    rw [if_pos rfl, if_neg hneq] at h
    exact one_ne_zero h
  · intro h c
    change (if @Quotient.mk _ (behSetoid S) x = c then 1 else 0) =
           (if @Quotient.mk _ (behSetoid S) y = c then 1 else 0)
    rw [show @Quotient.mk _ (behSetoid S) x = @Quotient.mk _ (behSetoid S) y from
        Quotient.sound h]

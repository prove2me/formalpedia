-- Prove2me | solution 1 for tropMatVecMul_shift_equivariant_nat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:40:20.26724+00:00
-- url     : https://prove2.me/submissions/cafc4826-8556-48fa-bdf5-5fc2c59a98a8

-- Sol generated from Cryptography/TropicalAlgebra/TropicalZKCommitments.lean
import Mathlib
import Definitions.Def_Cryptography_TropicalAlgebra_TropicalZKCommitments
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Zero-Knowledge Commitments

This file develops a theory of commitment schemes and zero-knowledge protocols
over the tropical (min-plus) semiring, establishing both impossibility results
for naïve Pedersen-style approaches and constructive alternatives based on
tropical matrix actions.

## Main Results

### Part I: Impossibility (Theorem A)
* `IdempotentSemiring` — class for semirings with `a + a = a`
* `idempotent_semiring_trivial_inverses` — additive inverses force triviality
* `tropical_pedersen_impossible` — linear homomorphic commitments with hiding
  are impossible in idempotent semirings

### Part II: Tropical Matrix Commitments (Theorem B)
* `tropMatVecMul` — tropical matrix-vector product
* `tropCommit` — tropical matrix commitment `C(x, r) = A ⊗ x ⊓ B ⊗ r`
* `tropCommit_binding_of_injective` — binding from injectivity of `A`-action
* `tropMatVecMul_shift_equivariant` — shift equivariance of tropical product

### Part III: Zero-Knowledge by Shift Invariance (Theorem C)
* `TropTranscript` — Σ-protocol transcript type
* `transcript_shift` — global shift action on transcripts
* `transcript_shift_preserves_verification` — shifted transcripts remain valid
* `tropical_sigma_zk` — zero-knowledge: every valid transcript has a
  shifted equivalent that is simulatable

### Part IV: Idempotent Normalization and Composition (Theorem D)
* `normalizeVec` — idempotent normalization (componentwise `⊓`)
* `normalizeVec_idem` — normalization is idempotent
* `compose_transcripts` — sequential composition of transcripts
* `parallel_soundness_decay` — soundness error decays exponentially
  under parallel repetition

## References

* Butkovič, P. "Max-linear Systems: Theory and Algorithms" (2010)
* Grigoriev & Shpilrain "Tropical Cryptography" (2014)
-/

open Finset Function

set_option linter.unusedVariables false

/-! ## Part I: Impossibility of Pedersen-style Commitments in Idempotent Semirings -/








/-! ## Part II: Tropical Matrix Commitment and Binding -/







/-
**Theorem B: Binding from injectivity of the message encoding.**

    If the tropical matrix-vector product `A ⊗ (·)` is injective on the
    message space, and the commitment values determine the `A`-component
    (i.e. the `B ⊗ r` part doesn't obscure the `A ⊗ x` part), then
    collisions in commitments force message equality.

    This replaces group cancellation with order-theoretic rigidity:
    injectivity of `tropMatVecMul A` is a tropical analogue of
    "full column rank".
-/

/-
Tropical matrix-vector product is shift-equivariant:
    `A ⊗ (x + c) = (A ⊗ x) + c` where `+ c` means adding a constant
    to each component.

    This is the foundation for zero-knowledge: shifting the input
    shifts the output uniformly.
-/

/-
When the `A`-component dominates (is ≤) the `B`-component,
    the commitment equals the `A`-component.
-/


/-! ## Part III: Zero-Knowledge by Tropical Shift Invariance -/








/-
**Theorem C (part 1): Shift preserves transcript structure.**
    Shifting a transcript by `s` and then by `t` is the same as
    shifting by `s + t`.
-/

/-
Shifting by zero is the identity.
-/

/-
**Theorem C (part 2): Zero-knowledge by shift invariance.**

    If a verifier is shift-invariant, then for any valid transcript `t`,
    there exists a "simulated" transcript `t'` that is a shifted version
    of `t`. This means the simulator can produce valid-looking transcripts
    by sampling a random shift.

    The key insight: in an idempotent setting, the shift acts as an
    exact algebraic symmetry (not just approximate/statistical), giving
    **perfect** zero-knowledge rather than computational ZK.
-/


/-! ## Part IV: Idempotent Normalization and Composition -/



/-
**Theorem D (part 1): Normalization is idempotent.**
    `normalize (normalize v) = normalize v`.
-/

/-
Normalization is the identity on `WithTop ℕ` (since `min` is idempotent).
-/



/-
**Theorem D (part 2): Soundness error decays under parallel repetition.**

    If a single-round protocol has soundness error at most `ε` (as a rational),
    meaning a cheating prover convinces the verifier with probability ≤ ε,
    then `k` independent parallel repetitions have soundness error ≤ ε^k.

    This is modeled finitely: if in each round, at most `num` out of `den`
    challenges pass for a cheating prover, then in `k` rounds, at most
    `num^k` out of `den^k` combined challenges pass.
-/

/-
The soundness ratio `num^k / den^k` equals `(num/den)^k`.
-/


/-! ## Part V: Connecting the Pieces -/


/-
The tropical commitment is monotone in the message:
    if `x₁ ≤ x₂` pointwise, then `Com(x₁, r) ≤ Com(x₂, r)` pointwise.
-/

/-
The tropical matrix-vector product is monotone.
-/

/-
The tropical commitment with a zero randomness vector equals
    the tropical matrix-vector product.
-/

/-
Shift equivariance of the commitment:
    `Com(x + c, r + c) = Com(x, r) + c` when A-component dominates.
-/


-- open removed: section is not a namespace
theorem solution    {m n : ℕ} (A : TropMat m n) (x : TropVec n) (c : ℕ) (i : Fin m) :
    tropMatVecMul A (fun j => x j + (c : Trop)) i =
    tropMatVecMul A x i + (c : Trop) := by
  unfold tropMatVecMul;
  rcases n with ( _ | n ) <;> simp_all +decide [ add_assoc, iInf ];
  rw [ @csInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
  · exact ⟨ _, ⟨ 0, rfl ⟩ ⟩;
  · rintro _ ⟨ j, rfl ⟩;
    simp +decide [ ← add_assoc ];
    exact csInf_le ⟨ 0, Set.forall_mem_range.mpr fun j => zero_le ⟩ ⟨ j, rfl ⟩;
  · intro w hw;
    -- Let $y$ be the infimum of the range of $A i j + x j$.
    set y := sInf (Set.range (fun j => A i j + x j)) with hy;
    -- Since $y$ is the infimum of the range of $A i j + x j$, there exists some $j$ such that $A i j + x j = y$.
    obtain ⟨j, hj⟩ : ∃ j, A i j + x j = y := by
      exact ( IsCompact.sInf_mem ( Set.finite_range _ |> Set.Finite.isCompact ) <| Set.nonempty_of_mem <| Set.mem_range_self <| 0 );
    exact ⟨ _, ⟨ j, rfl ⟩, by simpa [ ← add_assoc, hj ] using hw ⟩

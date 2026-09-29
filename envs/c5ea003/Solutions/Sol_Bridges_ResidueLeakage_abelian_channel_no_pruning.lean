-- Prove2me | solution 1 for Bridges.ResidueLeakage.abelian_channel_no_pruning
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:18:53.449611+00:00
-- url     : https://prove2.me/submissions/0e9faa4c-8bb5-4d30-9a85-4539f4866bf8

-- Sol generated from Bridges/AbelianChannelNoPruning.lean
import Mathlib
import Definitions.Def_Bridges_AbelianChannelNoPruning
/-
# The abelian channel no-pruning theorem

Fifth file of the residue-leakage thread.  This closes conjecture **C3** of
`FUTURE_DIRECTIONS.md` for a fixed conductor: the Dirichlet no-pruning
phenomenon is not about quadratic residues at all.  It holds for *every* finite
family of Dirichlet characters of a fixed modulus — i.e. for every abelian
residue channel of bounded conductor, in any coefficient ring.

Given probes `χ₁,…,χ_K : DirichletCharacter R M` define the *character
fingerprint* `Φ(N) = [χ_i(N)]`.  For a target `N₀` coprime to `M` and any
candidate prime `p ∤ M`, put `q` in the class `N₀ · p⁻¹ (mod M)`: then
`χ_i(pq) = χ_i(p)·χ_i(N₀ p⁻¹) = χ_i(N₀)` for every `i`, and Dirichlet's theorem
supplies infinitely many primes in that class.

The quadratic case (`Bridges.ResidueLeakageDirichletNoPruning`) is the special
case where each `χ_i` is the Jacobi symbol `(a_i | ·)` of conductor `4a_i`; there
`p⁻¹ ≡ p` up to squares, which is why the compensating class was `N₀ · p`.
-/


open Bridges.ResidueLeakage




/-! ## A quadratic instance: the supplementary symbol at `2` -/




open Bridges.ResidueLeakage in
theorem solution{R : Type*} [CommMonoidWithZero R] {M : ℕ}
    [NeZero M] (X : List (DirichletCharacter R M)) {N₀ p : ℕ}
    (hN₀ : Nat.Coprime N₀ M) (hpM : Nat.Coprime p M) :
    {q : ℕ | q.Prime ∧ charFingerprint X (p * q) = charFingerprint X N₀}.Infinite := by
  -- the compensating class `N₀ · p⁻¹`
  set u : (ZMod M)ˣ := ZMod.unitOfCoprime p hpM with hu
  set v : (ZMod M)ˣ := ZMod.unitOfCoprime N₀ hN₀ with hv
  have hup : ((u : ZMod M)) = (p : ZMod M) := rfl
  have hvN : ((v : ZMod M)) = (N₀ : ZMod M) := rfl
  have hunit : IsUnit (((v * u⁻¹ : (ZMod M)ˣ) : ZMod M)) := Units.isUnit _
  refine (Nat.infinite_setOf_prime_and_eq_mod hunit).mono ?_
  rintro q ⟨hq, hqc⟩
  refine ⟨hq, ?_⟩
  refine List.map_congr_left fun χ _ => ?_
  have hcast : ((p * q : ℕ) : ZMod M) = (p : ZMod M) * (q : ZMod M) := by push_cast; ring
  rw [hcast, hqc, map_mul]
  have hkey : (p : ZMod M) * ((v * u⁻¹ : (ZMod M)ˣ) : ZMod M) = (N₀ : ZMod M) := by
    have hgrp : (u * (v * u⁻¹) : (ZMod M)ˣ) = v := by
      rw [mul_comm v u⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    calc (p : ZMod M) * ((v * u⁻¹ : (ZMod M)ˣ) : ZMod M)
        = ((u * (v * u⁻¹) : (ZMod M)ˣ) : ZMod M) := by
          rw [Units.val_mul u (v * u⁻¹), hup]
      _ = (N₀ : ZMod M) := by rw [hgrp, hvN]
  rw [← map_mul, hkey]

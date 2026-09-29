-- Prove2me | solution 1 for Bridges.ResidueLeakage.infinite_primes_jacobi_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:28:40.408652+00:00
-- url     : https://prove2.me/submissions/04e0a472-867c-471a-aa71-846138af9bb7

-- Sol generated from Bridges/ResidueLeakageDirichletNoPruning.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Theorems.Thm_Bridges_ResidueLeakage_conductor_ne_zero
import Theorems.Thm_Bridges_ResidueLeakage_coprime_conductor
/-
# The Residue-Leakage Curve and the Dirichlet No-Pruning Theorem

Phase A research file (Bridges domain): bridging **quadratic residue theory /
Jacobi symbols**, **analytic number theory (Dirichlet's theorem on primes in
arithmetic progressions)** and **information-theoretic search pruning**.

## Setting

For a finite list `A` of primes (think: the first `K` primes `2,3,5,7,11,...`)
the *QR fingerprint* of `N` is
`F_A(N) = [ (a | N) : a ∈ A ]`, a list of Jacobi symbols; every entry is
computable in `poly(log N)` time, so `F_A` is the maximal *cheap* residue handle
attached to `N`.

The experimental claim under test (experiment QRLEAK) was:

* `F_A` has full discriminative power (on a finite sample it separates all `N`),
* but it yields **zero** reduction of the factor-candidate set.

We prove the second half as a theorem, and we *refute* the naive reading of the
first half: `F_A` is periodic modulo `4 * ∏ A`, hence massively non-injective —
every realised fingerprint class already contains infinitely many primes.

## Main results

* `qrFingerprint_mul` — the fingerprint is multiplicative in the modulus
  (the "symmetric residue structure": `F(pq) = F(p)·F(q)` entrywise).
* `qrFingerprint_of_modEq` — the fingerprint only depends on `N mod 4·∏A`
  (the conductor bound; for `A` containing `2` this is the classical `8·∏ a_i`).
* `infinite_primes_jacobi_eq` — **key lemma**: every residue-symbol pattern
  realised by *some* odd `N` coprime to `A` is realised by *infinitely many
  primes*.  (Dirichlet.)
* `dirichlet_no_pruning` — **main theorem**: for every `N₀` and *every* candidate
  prime `p`, there are infinitely many primes `q` with `F_A(p·q) = F_A(N₀)`.
  The fingerprint prunes nothing.
* `qrFingerprint_class_infinite` — the fingerprint is not a collision-free hash:
  each realised class contains infinitely many primes.
-/


open Bridges.ResidueLeakage

/-! ## Definitions -/






/-! ## Basic structure of the fingerprint -/





/-! ## Coprimality bookkeeping -/





/-! ## The Dirichlet realisation lemma -/



/-! ## Main theorem: no pruning -/





open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {m : ℕ} (hm : Odd m) (hcop : ∀ a ∈ A, Nat.Coprime m a) :
    {q : ℕ | q.Prime ∧ Odd q ∧
      ∀ a ∈ A, jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) m}.Infinite := by
  set M := qrConductor A with hM
  have hM0 : M ≠ 0 := conductor_ne_zero A hA
  have : NeZero M := ⟨hM0⟩
  have hunit : IsUnit ((m : ZMod M)) :=
    (ZMod.isUnit_iff_coprime m M).2 (coprime_conductor hm hcop)
  refine (Nat.infinite_setOf_prime_and_eq_mod hunit).mono ?_
  rintro q ⟨hq, hqm⟩
  have hmod : q ≡ m [MOD M] := (ZMod.natCast_eq_natCast_iff q m M).1 hqm
  have h2 : (2 : ℕ) ∣ M := ⟨2 * A.prod, by rw [hM, qrConductor]; ring⟩
  have hq2 : q % 2 = m % 2 := hmod.of_dvd h2
  have hqodd : Odd q := by
    rw [Nat.odd_iff] at hm ⊢; omega
  refine ⟨hq, hqodd, fun a ha => ?_⟩
  have hdvd : 4 * a ∣ M := mul_dvd_mul_left 4 (List.dvd_prod ha)
  have h' : q % (4 * a) = m % (4 * a) := hmod.of_dvd hdvd
  rw [jacobiSym.mod_right' a hqodd, jacobiSym.mod_right' a hm, h']

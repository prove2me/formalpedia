-- Prove2me | solution 1 for Bridges.ResidueLeakage.primeBasis_length
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:10.007908+00:00
-- url     : https://prove2.me/submissions/18c99153-b511-4756-be2e-c6419728f506

-- Sol generated from Bridges/ResidueLeakageDirichletNoPruning.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
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
@[simp] theorem solution(K : ℕ) : (primeBasis K).length = K := by
  simp [primeBasis]

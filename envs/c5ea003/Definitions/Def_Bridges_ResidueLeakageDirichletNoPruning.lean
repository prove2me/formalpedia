-- Prove2me | Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
-- name    : Bridges_ResidueLeakageDirichletNoPruning
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:30.67025+00:00
-- url     : https://prove2.me/theorems/1ac542d3-a3f5-4b3f-ba6a-a0513a7211a6
-- title:
--   Aether Catalog definitions — Bridges_ResidueLeakageDirichletNoPruning
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ResidueLeakageDirichletNoPruning`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ResidueLeakageDirichletNoPruning.lean by skeleton subtraction
import Mathlib
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


namespace Bridges.ResidueLeakage

/-! ## Definitions -/

/-- The QR fingerprint of `N` relative to a list `A` of "probe" primes:
the list of Jacobi symbols `(a | N)` for `a ∈ A`. -/
def qrFingerprint (A : List ℕ) (N : ℕ) : List ℤ :=
  A.map (fun a : ℕ => jacobiSym (a : ℤ) N)

/-- The conductor of the fingerprint: `4 * ∏ a`.  If `2 ∈ A` this is the
classical `8 * ∏_{a odd} a`. -/
def qrConductor (A : List ℕ) : ℕ := 4 * A.prod

/-- The list of the first `K` primes, `[2,3,5,7,...]`. -/
noncomputable def primeBasis (K : ℕ) : List ℕ :=
  (List.range K).map (Nat.nth Nat.Prime)



/-! ## Basic structure of the fingerprint -/





/-! ## Coprimality bookkeeping -/





/-! ## The Dirichlet realisation lemma -/



/-! ## Main theorem: no pruning -/




end Bridges.ResidueLeakage



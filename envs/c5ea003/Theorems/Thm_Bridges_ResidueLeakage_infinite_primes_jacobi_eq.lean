-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_infinite_primes_jacobi_eq
-- name    : Bridges.ResidueLeakage.infinite_primes_jacobi_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:32:08.505879+00:00
-- url     : https://prove2.me/theorems/2ad6d4c9-608a-4e05-b727-92dd3321af81
-- title:
--   Key lemma (Dirichlet).
-- statement:
--   **Key lemma (Dirichlet).**  Any pattern of Jacobi symbols realised by an odd
--   number `m` coprime to the probe primes is realised by infinitely many *primes*.
--
--   This is the analytic input: each entry of the fingerprint is a character of the
--   group `(ℤ/4∏A)ˣ`, and Dirichlet's theorem populates every unit class with
--   infinitely many primes.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.infinite_primes_jacobi_eq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       {m : ℕ} (hm : Odd m) (hcop : ∀ a ∈ A, Nat.Coprime m a) :
--       {q : ℕ | q.Prime ∧ Odd q ∧
--         ∀ a ∈ A, jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) m}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakageDirichletNoPruning.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakageDirichletNoPruning.lean#L138

-- Thm stub generated from Bridges/ResidueLeakageDirichletNoPruning.lean
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

theorem Bridges.ResidueLeakage.infinite_primes_jacobi_eq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {m : ℕ} (hm : Odd m) (hcop : ∀ a ∈ A, Nat.Coprime m a) :
    {q : ℕ | q.Prime ∧ Odd q ∧
      ∀ a ∈ A, jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) m}.Infinite := by sorry

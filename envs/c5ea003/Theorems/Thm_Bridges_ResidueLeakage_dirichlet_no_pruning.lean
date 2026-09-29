-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_dirichlet_no_pruning
-- name    : Bridges.ResidueLeakage.dirichlet_no_pruning
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:04.63456+00:00
-- url     : https://prove2.me/theorems/065df550-897a-4b23-b5f4-28b950eaf0bb
-- title:
--   Dirichlet no-pruning theorem.
-- statement:
--   **Dirichlet no-pruning theorem.**
--   Fix any target `N₀` (odd, coprime to the probe primes) and *any* candidate prime
--   `p` (odd, not itself a probe prime).  Then there are infinitely many primes `q`
--   such that the semiprime `p * q` has exactly the same QR fingerprint as `N₀`.
--
--   Consequently the observed fingerprint `F_A(N₀)`, however many probe primes it
--   uses, removes **no** candidate prime `p` from the divisor search: every `p`
--   remains consistent with the residue data.  The cheap residue channel has zero
--   pruning power.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.dirichlet_no_pruning{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       {N₀ p : ℕ} (hN₀ : Odd N₀) (hp : p.Prime) (hpodd : Odd p)
--       (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) (hpA : ∀ a ∈ A, a ≠ p) :
--       {q : ℕ | q.Prime ∧ qrFingerprint A (p * q) = qrFingerprint A N₀}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakageDirichletNoPruning.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakageDirichletNoPruning.lean#L183

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



/-! ## Main theorem: no pruning -/

theorem Bridges.ResidueLeakage.dirichlet_no_pruning{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {N₀ p : ℕ} (hN₀ : Odd N₀) (hp : p.Prime) (hpodd : Odd p)
    (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) (hpA : ∀ a ∈ A, a ≠ p) :
    {q : ℕ | q.Prime ∧ qrFingerprint A (p * q) = qrFingerprint A N₀}.Infinite := by sorry

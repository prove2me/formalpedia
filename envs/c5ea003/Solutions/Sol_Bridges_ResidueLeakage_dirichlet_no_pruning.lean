-- Prove2me | solution 1 for Bridges.ResidueLeakage.dirichlet_no_pruning
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:34:38.880905+00:00
-- url     : https://prove2.me/submissions/7a077c29-3f53-41d7-81e1-74b723e28e0b

-- Sol generated from Bridges/ResidueLeakageDirichletNoPruning.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Theorems.Thm_Bridges_ResidueLeakage_infinite_primes_jacobi_eq
import Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_congr
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

private theorem jacobi_prime_sq {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hne : a ≠ p) : jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p = 1 := by
  have hcop : Int.gcd (a : ℤ) (p : ℕ) = 1 := by
    simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes ha hp).2 hne
  rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;> rw [h] <;> norm_num




open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    {N₀ p : ℕ} (hN₀ : Odd N₀) (hp : p.Prime) (hpodd : Odd p)
    (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) (hpA : ∀ a ∈ A, a ≠ p) :
    {q : ℕ | q.Prime ∧ qrFingerprint A (p * q) = qrFingerprint A N₀}.Infinite := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hN0 : N₀ ≠ 0 := by rintro rfl; simp at hN₀
  set m := N₀ * p with hmdef
  have hmodd : Odd m := hN₀.mul hpodd
  have hmcop : ∀ a ∈ A, Nat.Coprime m a := fun a ha =>
    Nat.Coprime.mul_left (hNA a ha)
      ((Nat.coprime_primes hp (hA a ha)).2 (fun h => hpA a ha h.symm))
  refine (infinite_primes_jacobi_eq hA hmodd hmcop).mono ?_
  rintro q ⟨hq, hqodd, hsym⟩
  have hq0 : q ≠ 0 := hq.ne_zero
  have hNZp : NeZero p := ⟨hp0⟩
  have hNZq : NeZero q := ⟨hq0⟩
  have hNZN : NeZero N₀ := ⟨hN0⟩
  refine ⟨hq, qrFingerprint_congr fun a ha => ?_⟩
  calc jacobiSym (a : ℤ) (p * q)
      = jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) q := jacobiSym.mul_right _ _ _
    _ = jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) (N₀ * p) := by rw [hsym a ha]
    _ = jacobiSym (a : ℤ) N₀ * (jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p) := by
        rw [jacobiSym.mul_right (a : ℤ) N₀ p]; ring
    _ = jacobiSym (a : ℤ) N₀ := by
        rw [jacobi_prime_sq (hA a ha) hp (hpA a ha), mul_one]

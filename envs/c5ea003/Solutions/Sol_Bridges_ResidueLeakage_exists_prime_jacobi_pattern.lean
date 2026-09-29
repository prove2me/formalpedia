-- Prove2me | solution 1 for Bridges.ResidueLeakage.exists_prime_jacobi_pattern
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:30:42.301679+00:00
-- url     : https://prove2.me/submissions/1ad99a21-8c3f-41d1-8c3e-055a39aa7a5f

-- Sol generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_exists_modulus_jacobi_pattern
import Theorems.Thm_Bridges_ResidueLeakage_infinite_primes_jacobi_eq
/-
# Pattern surjectivity of the QR fingerprint, and the failure of individual pinning

Companion file to `Bridges.ResidueLeakageDirichletNoPruning`.

Where the no-pruning theorem shows that the cheap residue channel cannot *remove*
any candidate prime, this file shows the complementary, constructive fact: the
fingerprint map is **surjective onto all `2^K` sign patterns**, already on primes.
The proof is a genuine cross-domain bridge:

* Chinese remainder theorem (`existsCRT`) to build the residue class,
* quadratic reciprocity + the supplementary law at `2` (`jacobiSym.at_two`),
* existence of a quadratic nonresidue in a finite field
  (`FiniteField.exists_nonsquare`),
* Dirichlet's theorem (imported through `infinite_primes_jacobi_eq`).

Main results:

* `exists_prime_jacobi_pattern` — every prescribed sign pattern on a set of
  distinct odd probe primes, together with a prescribed value at `2`, is
  realised by infinitely many primes.
* `qrFingerprint_pattern_surjective` — the same for an arbitrary list of
  distinct probe primes (the prime `2` allowed): all `2^K` fingerprints occur.
* `no_individual_pinning` — for any observed `F_A(N₀)` and any probe prime `a₀`,
  there are consistent factorisations `p₁q₁` and `p₂q₂` of the *same*
  fingerprint with `(a₀|p₁) = 1` and `(a₀|p₂) = -1`: the data pins down no
  individual symbol of a factor, only the symmetric products.
-/


open Bridges.ResidueLeakage

/-! ## A Chinese remainder theorem for lists of moduli -/


/-! ## A quadratic nonresidue witness -/



/-! ## Building a modulus with a prescribed symbol pattern -/



/-! ## Pattern surjectivity on primes -/



/-! ## No individual pinning -/


/-! ## The exact range of the fingerprint -/



/-! ## Specialisation to the first `K` primes -/





open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (h2 : ∀ a ∈ A, a ≠ 2) (hnd : A.Nodup) {e₂ : ℤ} (he₂ : e₂ = 1 ∨ e₂ = -1)
    {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
    {q : ℕ | q.Prime ∧ Odd q ∧ jacobiSym 2 q = e₂ ∧
      ∀ a ∈ A, jacobiSym (a : ℤ) q = ε a}.Infinite := by
  obtain ⟨m, hmodd, hm2, hmA, hme₂, hmε⟩ :=
    exists_modulus_jacobi_pattern hA h2 hnd he₂ hε
  have hA' : ∀ a ∈ (2 :: A), a.Prime := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Nat.prime_two
    · exact hA a ha
  have hcop' : ∀ a ∈ (2 :: A), Nat.Coprime m a := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hm2
    · exact hmA a ha
  refine (infinite_primes_jacobi_eq hA' hmodd hcop').mono ?_
  rintro q ⟨hq, hqodd, hsym⟩
  refine ⟨hq, hqodd, ?_, ?_⟩
  · have := hsym 2 (by simp)
    simpa [hme₂] using this
  · intro a ha
    have := hsym a (by simp [ha])
    rw [this, hmε a ha]

-- Prove2me | solution 1 for Bridges.ResidueLeakage.no_individual_pinning
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:09.411673+00:00
-- url     : https://prove2.me/submissions/ef8ded4c-f3e4-4584-9134-fd2faf4a456a

-- Sol generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_exists_compensating_prime
import Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_pattern_surjective
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
    (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a)
    {a₀ : ℕ} (ha₀ : a₀ ∈ A) :
    ∃ p₁ q₁ p₂ q₂ : ℕ,
      p₁.Prime ∧ q₁.Prime ∧ p₂.Prime ∧ q₂.Prime ∧
      qrFingerprint A (p₁ * q₁) = qrFingerprint A N₀ ∧
      qrFingerprint A (p₂ * q₂) = qrFingerprint A N₀ ∧
      jacobiSym (a₀ : ℤ) p₁ = 1 ∧ jacobiSym (a₀ : ℤ) p₂ = -1 := by
  classical
  -- a prime with all symbols `+1`
  have hplus : ∀ ε : ℕ → ℤ, (∀ a ∈ A, ε a = 1 ∨ ε a = -1) →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ (∀ a ∈ A, a ≠ p) ∧
        ∀ a ∈ A, jacobiSym (a : ℤ) p = ε a := by
    intro ε hε
    obtain ⟨p, hp, hpodd, hpf⟩ :=
      (qrFingerprint_pattern_surjective hA hnd hε).nonempty
    have hsym : ∀ a ∈ A, jacobiSym (a : ℤ) p = ε a := fun a ha =>
      List.map_inj_left.1 hpf a ha
    refine ⟨p, hp, hpodd, ?_, hsym⟩
    intro a ha hap
    have h0 : jacobiSym (a : ℤ) p = 0 := by
      subst hap
      haveI : NeZero a := ⟨(hA a ha).ne_zero⟩
      rw [jacobiSym.eq_zero_iff_not_coprime]
      simp [(hA a ha).one_lt.ne']
    rcases hε a ha with h | h <;> rw [hsym a ha, h] at h0 <;> norm_num at h0
  obtain ⟨p₁, hp₁, hp₁odd, hp₁ne, hp₁sym⟩ := hplus (fun _ => 1) (by intro a _; left; rfl)
  obtain ⟨p₂, hp₂, hp₂odd, hp₂ne, hp₂sym⟩ :=
    hplus (fun a => if a = a₀ then -1 else 1) (by
      intro a _; by_cases h : a = a₀ <;> simp [h])
  obtain ⟨q₁, hq₁, hq₁f⟩ :=
    exists_compensating_prime hA hN₀ hp₁ hp₁odd hNA hp₁ne
  obtain ⟨q₂, hq₂, hq₂f⟩ :=
    exists_compensating_prime hA hN₀ hp₂ hp₂odd hNA hp₂ne
  refine ⟨p₁, q₁, p₂, q₂, hp₁, hq₁, hp₂, hq₂, hq₁f, hq₂f, ?_, ?_⟩
  · simpa using hp₁sym a₀ ha₀
  · simpa using hp₂sym a₀ ha₀

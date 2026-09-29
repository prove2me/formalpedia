-- Prove2me | solution 1 for Bridges.ResidueLeakage.qrFingerprint_pattern_surjective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:32:01.856829+00:00
-- url     : https://prove2.me/submissions/91f616d9-e5bc-4f05-837e-321a92729bcd

-- Sol generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_exists_prime_jacobi_pattern
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
    (hnd : A.Nodup) {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
    {q : ℕ | q.Prime ∧ Odd q ∧ qrFingerprint A q = A.map ε}.Infinite := by
  classical
  set B := A.filter (fun a => decide (a ≠ 2)) with hB
  have hBsub : ∀ a ∈ B, a ∈ A := fun a ha => List.mem_of_mem_filter ha
  have hBprime : ∀ a ∈ B, a.Prime := fun a ha => hA a (hBsub a ha)
  have hB2 : ∀ a ∈ B, a ≠ 2 := by
    intro a ha
    have := List.of_mem_filter ha
    simpa using this
  have hBnd : B.Nodup := hnd.filter _
  have hBε : ∀ a ∈ B, ε a = 1 ∨ ε a = -1 := fun a ha => hε a (hBsub a ha)
  -- prescribe the value at `2`
  set e₂ : ℤ := if 2 ∈ A then ε 2 else 1 with he₂def
  have he₂ : e₂ = 1 ∨ e₂ = -1 := by
    by_cases h : 2 ∈ A
    · simp only [he₂def, if_pos h]; exact hε 2 h
    · left; simp [he₂def, h]
  refine (exists_prime_jacobi_pattern hBprime hB2 hBnd he₂ hBε).mono ?_
  rintro q ⟨hq, hqodd, hq2, hqB⟩
  refine ⟨hq, hqodd, ?_⟩
  simp only [qrFingerprint]
  refine List.map_congr_left fun a ha => ?_
  by_cases ha2 : a = 2
  · subst ha2
    have : e₂ = ε 2 := by simp [he₂def, ha]
    rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num, hq2, this]
  · have haB : a ∈ B := List.mem_filter.2 ⟨ha, by simpa using ha2⟩
    exact hqB a haB

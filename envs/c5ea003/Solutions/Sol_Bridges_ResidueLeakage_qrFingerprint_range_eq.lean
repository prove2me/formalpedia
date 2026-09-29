-- Prove2me | solution 1 for Bridges.ResidueLeakage.qrFingerprint_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:34:38.250338+00:00
-- url     : https://prove2.me/submissions/7e5794ef-6af1-4b95-906b-e10abb50dcab

-- Sol generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_exists_map_eq_of_nodup
import Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_length
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
    (hnd : A.Nodup) :
    {v : List ℤ | ∃ q : ℕ, q.Prime ∧ q ∉ A ∧ qrFingerprint A q = v}
      = {v : List ℤ | v.length = A.length ∧ ∀ x ∈ v, x = 1 ∨ x = -1} := by
  ext v
  constructor
  · rintro ⟨q, hq, hqA, rfl⟩
    refine ⟨by simp, ?_⟩
    intro x hx
    simp only [qrFingerprint, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hne : a ≠ q := fun h => hqA (h ▸ ha)
    have hcop : Int.gcd (a : ℤ) (q : ℕ) = 1 := by
      simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes (hA a ha) hq).2 hne
    exact jacobiSym.eq_one_or_neg_one hcop
  · rintro ⟨hlen, hv⟩
    obtain ⟨ε, hε⟩ := exists_map_eq_of_nodup A hnd v hlen
    have hεA : ∀ a ∈ A, ε a = 1 ∨ ε a = -1 := by
      intro a ha
      exact hv (ε a) (hε ▸ List.mem_map_of_mem ha)
    obtain ⟨q, hq, -, hqf⟩ :=
      (qrFingerprint_pattern_surjective hA hnd hεA).nonempty
    refine ⟨q, hq, ?_, by rw [hqf, hε]⟩
    intro hqA
    have h0 : jacobiSym (q : ℤ) q = 0 := by
      haveI : NeZero q := ⟨hq.ne_zero⟩
      rw [jacobiSym.eq_zero_iff_not_coprime]
      simp [hq.one_lt.ne']
    have hval : jacobiSym (q : ℤ) q = ε q := List.map_inj_left.1 hqf q hqA
    rcases hεA q hqA with h | h <;> rw [hval, h] at h0 <;> norm_num at h0

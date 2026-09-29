-- Prove2me | solution 1 for Bridges.ResidueLeakage.existsCRT
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:24:30.733354+00:00
-- url     : https://prove2.me/submissions/a99045fc-908e-473a-8a6f-00e9e4868abb

-- Sol generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_coprime_list_prod
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
theorem solution: ∀ (L : List ℕ), L.Pairwise Nat.Coprime → ∀ f : ℕ → ℕ,
    ∃ m : ℕ, ∀ x ∈ L, m ≡ f x [MOD x] := by
  intro L
  induction L with
  | nil => intro _ f; exact ⟨0, by simp⟩
  | cons a t ih =>
      intro hcop f
      obtain ⟨mt, hmt⟩ := ih hcop.of_cons f
      have hat : Nat.Coprime a t.prod :=
        coprime_list_prod fun b hb => (List.pairwise_cons.1 hcop).1 b hb
      obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hat (f a) mt
      refine ⟨k, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hk1
      · exact (hk2.of_dvd (List.dvd_prod hx)).trans (hmt x hx)

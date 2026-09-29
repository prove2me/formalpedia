-- Prove2me | solution 1 for Bridges.ResidueLeakage.exists_map_eq_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:22:04.927819+00:00
-- url     : https://prove2.me/submissions/b7f7dcdf-200c-494b-8fd5-2910002e2abc

-- Sol generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
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
theorem solution: ∀ (A : List ℕ), A.Nodup → ∀ v : List ℤ,
    v.length = A.length → ∃ ε : ℕ → ℤ, A.map ε = v := by
  classical
  intro A
  induction A with
  | nil => intro _ v hv; exact ⟨fun _ => 0, by simpa using (List.length_eq_zero_iff.1 hv).symm⟩
  | cons a t ih =>
      intro hnd v hv
      obtain ⟨x, w, rfl⟩ : ∃ x w, v = x :: w := by
        cases v with
        | nil => simp at hv
        | cons x w => exact ⟨x, w, rfl⟩
      have hant : a ∉ t := (List.nodup_cons.1 hnd).1
      obtain ⟨ε', hε'⟩ := ih (List.nodup_cons.1 hnd).2 w (by simpa using hv)
      refine ⟨fun y => if y = a then x else ε' y, ?_⟩
      have ht : t.map (fun y => if y = a then x else ε' y) = t.map ε' :=
        List.map_congr_left fun b hb => by
          have : b ≠ a := fun h => hant (h ▸ hb)
          simp [this]
      simp [ht, hε']

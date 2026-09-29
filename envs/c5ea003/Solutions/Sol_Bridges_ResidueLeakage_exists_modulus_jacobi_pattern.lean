-- Prove2me | solution 1 for Bridges.ResidueLeakage.exists_modulus_jacobi_pattern
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:26:59.835034+00:00
-- url     : https://prove2.me/submissions/7d710602-faba-4d7b-a9d4-a9a33b9bc0d9

-- Sol generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Theorems.Thm_Bridges_ResidueLeakage_existsCRT
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


theorem legendreSym_nonresidueWitness (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) :
    legendreSym p (nonresidueWitness p) = -1 := by
  have hex : ∃ r : ℕ, ¬ IsSquare ((r : ZMod p)) := by
    obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by simpa [ZMod.ringChar_zmod_n] using h2)
    exact ⟨x.val, by simpa using hx⟩
  have : nonresidueWitness p = hex.choose := by
    simp [nonresidueWitness, dif_pos hex]
  rw [this, legendreSym.eq_neg_one_iff]
  simpa using hex.choose_spec

/-! ## Building a modulus with a prescribed symbol pattern -/



/-! ## Pattern surjectivity on primes -/



/-! ## No individual pinning -/


/-! ## The exact range of the fingerprint -/



/-! ## Specialisation to the first `K` primes -/





open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (h2 : ∀ a ∈ A, a ≠ 2) (hnd : A.Nodup) {e₂ : ℤ} (he₂ : e₂ = 1 ∨ e₂ = -1)
    {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
    ∃ m : ℕ, Odd m ∧ Nat.Coprime m 2 ∧ (∀ a ∈ A, Nat.Coprime m a) ∧
      jacobiSym 2 m = e₂ ∧ ∀ a ∈ A, jacobiSym (a : ℤ) m = ε a := by
  classical
  set f := patternResidue e₂ ε with hf
  -- the list of moduli `8 :: A` is pairwise coprime
  have hApw : A.Pairwise Nat.Coprime :=
    hnd.imp_of_mem fun {a b} ha hb hne => (Nat.coprime_primes (hA a ha) (hA b hb)).2 hne
  have hcop8 : ∀ a ∈ A, Nat.Coprime 8 a := by
    intro a ha
    have hodd : Odd a := (hA a ha).odd_of_ne_two (h2 a ha)
    have : Nat.Coprime a 2 := Nat.coprime_two_right.2 hodd
    have h2a : Nat.Coprime 2 a := this.symm
    have := (h2a.pow_left 3)
    norm_num at this
    exact this
  have hpw : (8 :: A).Pairwise Nat.Coprime := List.pairwise_cons.2 ⟨hcop8, hApw⟩
  obtain ⟨m, hm⟩ := existsCRT (8 :: A) hpw f
  have hm8 : m ≡ f 8 [MOD 8] := hm 8 (by simp)
  have hf8 : f 8 = if e₂ = 1 then 1 else 5 := by simp [hf, patternResidue]
  -- `m % 8 ∈ {1, 5}`, according to the prescribed sign at `2`
  have hm8' : m % 8 = f 8 % 8 := hm8
  have hcase : (e₂ = 1 ∧ m % 8 = 1) ∨ (e₂ = -1 ∧ m % 8 = 5) := by
    rcases he₂ with h | h
    · refine Or.inl ⟨h, ?_⟩
      have hfe : f 8 = 1 := by rw [hf8, if_pos h]
      rw [hm8', hfe]
    · refine Or.inr ⟨h, ?_⟩
      have hfe : f 8 = 5 := by rw [hf8, if_neg (by rw [h]; norm_num)]
      rw [hm8', hfe]
  have hmod8 : m % 8 = 1 ∨ m % 8 = 5 := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hmodd : Odd m := by rw [Nat.odd_iff]; omega
  have hm4 : m % 4 = 1 := by omega
  -- the value at 2
  have hat2 : jacobiSym 2 m = e₂ := by
    rw [jacobiSym.at_two hmodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hm2 : m % 2 = 1 := Nat.odd_iff.1 hmodd
    rcases hcase with ⟨he, h8⟩ | ⟨he, h8⟩
    · rw [he]; simp [hm2, h8]
    · rw [he]; simp [hm2, h8]
  -- the values at the odd probe primes
  have hatodd : ∀ a ∈ A, jacobiSym (a : ℤ) m = ε a := by
    intro a ha
    haveI : Fact a.Prime := ⟨hA a ha⟩
    have hodd : Odd a := (hA a ha).odd_of_ne_two (h2 a ha)
    have hrec : jacobiSym (m : ℤ) a = jacobiSym (a : ℤ) m :=
      jacobiSym.quadratic_reciprocity_one_mod_four hm4 hodd
    have hleg : jacobiSym (a : ℤ) m = legendreSym a (m : ℤ) := by
      rw [← hrec, jacobiSym.legendreSym.to_jacobiSym]
    have hcong : m ≡ f a [MOD a] := hm a (by simp [ha])
    have hint : (m : ℤ) % (a : ℤ) = ((f a : ℕ) : ℤ) % (a : ℤ) := by
      have := hcong
      unfold Nat.ModEq at this
      exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this
    have hmodeq : legendreSym a (m : ℤ) = legendreSym a ((f a : ℕ) : ℤ) := by
      rw [legendreSym.mod a (m : ℤ), legendreSym.mod a ((f a : ℕ) : ℤ), hint]
    have ha8 : a ≠ 8 := by
      intro h
      have h8 : Nat.Prime 8 := h ▸ hA a ha
      norm_num at h8
    rcases hε a ha with hεa | hεa
    · have hfa : f a = 1 := by simp [hf, patternResidue, ha8, hεa]
      rw [hleg, hmodeq, hfa, hεa]
      simp
    · have hfa : f a = nonresidueWitness a := by
        simp [hf, patternResidue, ha8, hεa]
      rw [hleg, hmodeq, hfa, hεa]
      exact legendreSym_nonresidueWitness a (h2 a ha)
  -- coprimality follows from the symbols being nonzero
  have hm0 : m ≠ 0 := by intro h; rw [h] at hmod8; simp at hmod8
  have : NeZero m := ⟨hm0⟩
  have hcopA : ∀ a ∈ A, Nat.Coprime m a := by
    intro a ha
    have hne : jacobiSym (a : ℤ) m ≠ 0 := by
      rw [hatodd a ha]; rcases hε a ha with h | h <;> rw [h] <;> norm_num
    have := (jacobiSym.eq_zero_iff_not_coprime (a := (a : ℤ)) (b := m)).not.1 hne
    rw [not_not] at this
    have hgcd : Nat.gcd a m = 1 := by simpa [Int.gcd_natCast_natCast] using this
    exact (Nat.coprime_iff_gcd_eq_one.2 hgcd).symm
  exact ⟨m, hmodd, Nat.coprime_two_right.2 hmodd, hcopA, hat2, hatodd⟩

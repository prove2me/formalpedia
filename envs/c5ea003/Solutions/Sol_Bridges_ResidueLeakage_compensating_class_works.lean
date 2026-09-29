-- Prove2me | solution 1 for Bridges.ResidueLeakage.compensating_class_works
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:22:02.860282+00:00
-- url     : https://prove2.me/submissions/49af155b-0f31-4fb9-97c2-7e6387ac2af1

-- Sol generated from Bridges/ResidueLeakageEffective.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_congr
/-
# The compensator lives in a single unit class: effective no-pruning (conjecture C1)

Ninth file of the residue-leakage thread.  `dirichlet_no_pruning` is purely
existential: it invokes Dirichlet's theorem to produce a compensating prime `q`
with `F_A(p·q) = F_A(N₀)`, with no control on the size of `q`.  Conjecture C1 of
`FUTURE_DIRECTIONS.md` asks for an *effective* version.

This file isolates exactly the arithmetic content of that conjecture and
reduces it to a statement about primes in arithmetic progressions:

* `compensating_class_coprime` / `compensating_class_works` — the compensating
  set is a **full unit class modulo the conductor**: *every* prime
  `q ≡ N₀·p (mod 4∏A)` compensates, and `N₀·p` is a unit mod `4∏A`.
  No analytic input at all is used here; this is a congruence statement.
* `effective_no_pruning_of_linnik` — consequently, *any* effective bound `B` for
  the least prime in a coprime residue class modulo `4∏A` is inherited verbatim
  by the compensator.  Linnik's theorem (`B = C·M^L`) therefore turns
  no-pruning into a constructive, polynomial-time defeat of the residue sieve.
  The hypothesis is a genuine (classically true) statement about the modulus
  `4∏A`, supplied as an explicit assumption rather than assumed as an axiom.
* `no_pruning_of_dirichlet_class` — conversely, the qualitative theorem is
  recovered from the same lemma plus infinitude of primes in the class, showing
  that the congruence lemma is the *whole* non-analytic content of no-pruning.
-/


open Bridges.ResidueLeakage

variable {A : List ℕ}






open Bridges.ResidueLeakage in
theorem solution(hA : ∀ a ∈ A, a.Prime) {N₀ p q : ℕ}
    (hN₀ : Odd N₀) (hp : p.Prime) (hpodd : Odd p) (hq : q.Prime)
    (hpA : ∀ a ∈ A, a ≠ p) (hcong : q ≡ N₀ * p [MOD qrConductor A]) :
    qrFingerprint A (p * q) = qrFingerprint A N₀ := by
  have hN0 : N₀ ≠ 0 := by rintro rfl; simp at hN₀
  haveI : NeZero N₀ := ⟨hN0⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hmodd : Odd (N₀ * p) := hN₀.mul hpodd
  -- `q` is odd because `2 ∣ 4∏A`
  have h2 : (2 : ℕ) ∣ qrConductor A := ⟨2 * A.prod, by rw [qrConductor]; ring⟩
  have hqodd : Odd q := by
    have h2' : q % 2 = (N₀ * p) % 2 := hcong.of_dvd h2
    rw [Nat.odd_iff] at hmodd ⊢
    omega
  -- the fingerprint only sees the class mod `4a` for each probe `a`
  have hsym : ∀ a ∈ A, jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) (N₀ * p) := by
    intro a ha
    have hdvd : 4 * a ∣ qrConductor A := mul_dvd_mul_left 4 (List.dvd_prod ha)
    have h' : q % (4 * a) = (N₀ * p) % (4 * a) := hcong.of_dvd hdvd
    rw [jacobiSym.mod_right' a hqodd, jacobiSym.mod_right' a hmodd, h']
  refine qrFingerprint_congr fun a ha => ?_
  have hsq : jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p = 1 := by
    have hcop : Int.gcd (a : ℤ) (p : ℕ) = 1 := by
      simpa [Int.gcd_natCast_natCast] using
        (Nat.coprime_primes (hA a ha) hp).2 (hpA a ha)
    rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;> rw [h] <;> norm_num
  calc jacobiSym (a : ℤ) (p * q)
      = jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) q := jacobiSym.mul_right _ _ _
    _ = jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) (N₀ * p) := by rw [hsym a ha]
    _ = jacobiSym (a : ℤ) N₀ * (jacobiSym (a : ℤ) p * jacobiSym (a : ℤ) p) := by
        rw [jacobiSym.mul_right (a : ℤ) N₀ p]; ring
    _ = jacobiSym (a : ℤ) N₀ := by rw [hsq, mul_one]

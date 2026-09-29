-- Prove2me | solution 1 for PrimeGapCrossword.explicit_forcing_23_alt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:52.747508+00:00
-- url     : https://prove2.me/submissions/d5b1c768-3607-435c-9029-aff3a9d5b932

-- Sol generated from Speculative/NumberTheory/PrimeGapCrosswordDeep.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_PrimeGapCrosswordDeep
/-
# Prime Gap Crossword: Deep Structure and Automaton Theory

This module develops the automaton-theoretic view of prime gap patterns.
The key insight: fixing a sieve set S of small primes, the admissibility
of a gap word is determined by a finite-state automaton whose states are
residue classes mod ∏S. This turns the "prime crossword" into a problem
in symbolic dynamics over a finite alphabet.

## Main results

1. **GapAutomaton**: A finite-state machine tracking admissible residue
   classes as gaps are consumed.

2. **Consecutive gap sum bound**: For primes p > 3, consecutive gaps sum ≥ 4.

3. **Residue class analysis**: Primes mod 6 and mod 30.

4. **Twin prime residue theorem**: twin primes > 3 are ≡ 5 mod 6.

5. **Sieve admissibility framework**: modular sieve analysis of prime gaps.

6. **Explicit forcing patterns**: concrete gap sequences that determine the next gap.
-/


open Finset Nat

open PrimeGapCrossword

/-! ## Core Sieve Definitions -/












/-! ## Section 1: Prime gap basic properties -/



/-! ## Section 2: Modular residue analysis -/

/-
A prime p > 3 satisfies p ≡ 1 or 5 (mod 6).
-/


/-! ## Section 3: Twin prime residue theorem -/

/-
If p and p+2 are both prime with p > 3, then p ≡ 5 (mod 6).
-/


/-! ## Section 4: The Gap Automaton -/



/-
A forcing state has a unique residue.
-/

/-! ## Section 5: Residue counting -/

/-
For a single prime q, the number of residues in [0, q) avoiding q
    is exactly q - 1.
-/

/-! ## Section 6: Prime residues mod 30 -/

/-
A prime p > 5 satisfies p mod 30 ∈ {1, 7, 11, 13, 17, 19, 23, 29}.
-/


/-! ## Section 7: Sieve monotonicity -/



/-! ## Section 8: Admissibility periodicity -/

/-
Admissibility is periodic: if M divides all primes in S, then
    admissible at a implies admissible at a + M.
-/

/-
If a gap word is S-admissible, there are infinitely many
    starting positions realizing it.
-/

/-! ## Section 9: Explicit forcing patterns -/

/-
Over {2,3} with bound 6, [2] forces next gap 4.
-/

/-
Over {2,3} with bound 6, [4] forces next gap 2.
-/


/-! ## Section 10: Forcing transfer -/


/-! ## Section 11: Forcing Density Conjecture -/




open PrimeGapCrossword in
theorem solution:
    ForcingNextOver {2, 3} 6 [4] 2 := by
      constructor;
      · use 1; simp +decide [ AdmissibleAt ] ;
      · intro h h_pos h_le;
        interval_cases h <;> simp_all +decide [ NextGapAdmissibleOver ];
        · unfold AdmissibleOver;
          unfold AdmissibleAt; simp +decide [ gapWordPositions, interiorSet ] ;
          intro x hx₁ hx₂ hx₃; use 2; simp_all +decide [ AvoidsPrimes, HitByPrimes ] ;
        · rintro ⟨ a, ha ⟩;
          obtain ⟨ h₁, h₂ ⟩ := ha;
          unfold gapWordPositions interiorSet at * ; simp_all +decide [ AvoidsPrimes, HitByPrimes ];
          omega;
        · unfold AdmissibleOver;
          unfold AdmissibleAt; simp +decide [ gapWordPositions, interiorSet ] ;
          intro x hx₁ hx₂ hx₃; use if x % 2 = 0 then 1 else 2; simp_all +decide [ AvoidsPrimes, HitByPrimes ] ;
        · rintro ⟨ a, ha ⟩;
          unfold AdmissibleAt at ha;
          unfold gapWordPositions interiorSet at ha ; simp_all +decide [ AvoidsPrimes, HitByPrimes ];
          grind;
        · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩ ⟩;
          have := ha₂ 1; have := ha₂ 2; have := ha₂ 3; have := ha₂ 5; have := ha₂ 6; have := ha₂ 7; have := ha₂ 8; have := ha₂ 9; simp_all +decide [ HitByPrimes ] ;
          grind +splitImp

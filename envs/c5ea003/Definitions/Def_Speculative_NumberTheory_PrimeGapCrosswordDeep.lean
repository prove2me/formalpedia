-- Prove2me | Definitions.Def_Speculative_NumberTheory_PrimeGapCrosswordDeep
-- name    : Speculative_NumberTheory_PrimeGapCrosswordDeep
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:21.296424+00:00
-- url     : https://prove2.me/theorems/2b9a01ba-731e-41f1-b04f-3ad6345efc30
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_PrimeGapCrosswordDeep
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.PrimeGapCrosswordDeep`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/PrimeGapCrosswordDeep.lean by skeleton subtraction
import Mathlib
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

namespace PrimeGapCrossword

/-! ## Core Sieve Definitions -/

/-- Cumulative sums of a gap word, starting from 0. -/
def gapWordPositions (gaps : List ℕ) : List ℕ :=
  gaps.scanl (· + ·) 0

/-- The set of all integers strictly between consecutive cumulative positions. -/
def interiorSet (gaps : List ℕ) : Finset ℕ :=
  let positions := gapWordPositions gaps
  let pairs := positions.zip positions.tail
  pairs.foldl (fun acc (p : ℕ × ℕ) =>
    acc ∪ (Finset.Ioo p.1 p.2)) ∅

/-- A number avoids all primes in a finite set S. -/
def AvoidsPrimes (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ q ∈ S, ¬(q ∣ n)

/-- A number is hit by at least one prime in S. -/
def HitByPrimes (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ q ∈ S, q ∣ n

instance (S : Finset ℕ) (n : ℕ) : Decidable (AvoidsPrimes S n) :=
  inferInstanceAs (Decidable (∀ q ∈ S, ¬(q ∣ n)))

instance (S : Finset ℕ) (n : ℕ) : Decidable (HitByPrimes S n) :=
  inferInstanceAs (Decidable (∃ q ∈ S, q ∣ n))

/-- A gap word is S-admissible at residue a. -/
def AdmissibleAt (S : Finset ℕ) (gaps : List ℕ) (a : ℕ) : Prop :=
  (∀ t ∈ gapWordPositions gaps, AvoidsPrimes S (a + t)) ∧
  (∀ u ∈ interiorSet gaps, HitByPrimes S (a + u))

instance (S : Finset ℕ) (gaps : List ℕ) (a : ℕ) : Decidable (AdmissibleAt S gaps a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A gap word is S-admissible if some starting residue works. -/
def AdmissibleOver (S : Finset ℕ) (gaps : List ℕ) : Prop :=
  ∃ a : ℕ, AdmissibleAt S gaps a

/-- A gap g is an admissible next gap after word w over sieve S. -/
def NextGapAdmissibleOver (S : Finset ℕ) (w : List ℕ) (g : ℕ) : Prop :=
  AdmissibleOver S (w ++ [g])

/-- A bounded next-gap g is "forcing" for word w over S with bound B:
    g is the unique positive admissible next gap ≤ B. -/
def ForcingNextOver (S : Finset ℕ) (B : ℕ) (w : List ℕ) (g : ℕ) : Prop :=
  NextGapAdmissibleOver S w g ∧
  ∀ h : ℕ, 0 < h → h ≤ B → NextGapAdmissibleOver S w h → h = g

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

/-- The state of a gap automaton: a set of candidate starting residues mod M. -/
structure GapAutomatonState (M : ℕ) where
  admissibleResidues : Finset (Fin M)
  deriving DecidableEq

/-- A state is forcing if it has exactly one admissible residue. -/
def GapAutomatonState.isForcing {M : ℕ} (s : GapAutomatonState M) : Prop :=
  s.admissibleResidues.card = 1

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



end PrimeGapCrossword



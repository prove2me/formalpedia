-- Prove2me | Definitions.Def_Speculative_NumberTheory_PrimeGapAutomaton
-- name    : Speculative_NumberTheory_PrimeGapAutomaton
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:57:53.576059+00:00
-- url     : https://prove2.me/theorems/fb836737-bc27-4ac7-9d6e-39b4589866f1
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_PrimeGapAutomaton
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.PrimeGapAutomaton`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/PrimeGapAutomaton.lean by skeleton subtraction
import Mathlib
/-
# Prime Gap Automaton Theory: Modular Constraints as Symbolic Dynamics

This module develops the theory of prime gap sequences viewed through the lens
of finite-state automata and symbolic dynamics. The central construction is
the **Residue Transition System** (RTS): given a modulus m (typically a
primorial like 6, 30, or 210), consecutive primes trace a path through
the coprime residues mod m, and the gap sequence is the sequence of "steps."

## Main results

1. **Mod-6 Automaton Correctness**: The 2-state automaton exactly captures
   all mod-6 constraints on prime gap sequences.
2. **Bertrand Gap Bound**: Every prime gap g(p) < p.
3. **Twin Prime Isolation**: Gaps adjacent to twin primes must be ≥ 4.
4. **Forbidden Patterns**: [2,2], [4,4], [2,4,2] are forbidden gap sequences.
5. **Cousin Prime Classification**: Cousin primes require state 1 mod 6.

## Novel definitions

- `ResidueTransitionSystem`: Finite-state machine for prime gap constraints.
- `Mod6State` / `mod6Transition`: The explicit 2-state automaton for mod-6.
-/


open Finset Nat

namespace PrimeGapAutomaton

/-! ## Section 1: Residue Transition System -/

/-- **Novel Structure**: A Residue Transition System (RTS) captures
    the finite-state automaton induced by a modulus m on prime gap sequences.
    States are coprime residue classes; transitions are gap values. -/
structure ResidueTransitionSystem where
  /-- The modulus (typically a primorial) -/
  modulus : ℕ
  /-- The modulus is at least 2 -/
  modulus_pos : 2 ≤ modulus
  /-- The set of admissible residues (coprime to modulus) -/
  states : Finset ℕ
  /-- All states are less than the modulus -/
  states_bound : ∀ s ∈ states, s < modulus
  /-- States are coprime to the modulus -/
  states_coprime : ∀ s ∈ states, Nat.Coprime s modulus

/-- The mod-6 RTS. States are {1, 5} = units of ℤ/6ℤ. -/
def RTS6 : ResidueTransitionSystem where
  modulus := 6
  modulus_pos := by norm_num
  states := {1, 5}
  states_bound := by decide
  states_coprime := by decide

/-- The mod-30 RTS. States are {1,7,11,13,17,19,23,29} = units of ℤ/30ℤ. -/
def RTS30 : ResidueTransitionSystem where
  modulus := 30
  modulus_pos := by norm_num
  states := {1, 7, 11, 13, 17, 19, 23, 29}
  states_bound := by decide
  states_coprime := by decide


/-! ## Section 2: Bertrand's Gap Bound -/

/-
**Bertrand Gap Bound**: For consecutive primes p < q, gap q - p < p.
-/

/-! ## Section 3: Mod-6 State Classification -/

/-
Every prime > 3 is ≡ 1 or 5 mod 6.
-/

/-
A gap of 2 from state 1 is impossible (p+2 ≡ 0 mod 3).
-/

/-
A gap of 4 from state 5 is impossible (p+4 ≡ 0 mod 3).
-/

/-! ## Section 4: The Mod-6 Automaton -/

/-- The mod-6 state: either residue 1 or residue 5. -/
inductive Mod6State
  | one  -- p ≡ 1 mod 6
  | five -- p ≡ 5 mod 6
  deriving DecidableEq, Repr

/-- The transition function of the mod-6 automaton. -/
def mod6Transition (s : Mod6State) (gapMod6 : ℕ) : Option Mod6State :=
  match s, gapMod6 with
  | .one,  0 => some .one
  | .one,  4 => some .five
  | .five, 0 => some .five
  | .five, 2 => some .one
  | _,     _ => none

/-
**Mod-6 Automaton Correctness**: The transition function exactly
    captures the mod-6 constraint on prime gap sequences.
-/

/-! ## Section 5: Gap Alternation Theorems -/

/-
**Gap Alternation from State 1**: Gap ≡ 0 stays at 1, gap ≡ 4 goes to 5.
-/

/-
**Gap Alternation from State 5**: Gap ≡ 0 stays at 5, gap ≡ 2 goes to 1.
-/

/-! ## Section 6: Twin Prime Isolation -/


/-
**Twin Prime Isolation (Forward)**: After twin primes (p, p+2)
    with p > 3, the next prime is at least p+6.
-/

/-
**Twin Prime Isolation (Backward)**: Before twin primes (q, q+2)
    with q > 3, the previous prime p (> 3) satisfies p + 4 ≤ q.
-/

/-! ## Section 7: Forbidden Patterns -/



/- Note: The pattern [2,4,2] is NOT forbidden — (11,13,17,19) is a valid instance.
   Instead, we prove [2,4,2,4,2] is forbidden for p > 5: the six numbers
   p, p+2, p+6, p+8, p+12, p+14 cover all residues mod 5. -/


/-
**Forbidden Pattern [2,4,2,4,2]**: For p > 5, not all of
    p, p+2, p+6, p+8, p+12, p+14 can be prime.
-/

/-! ## Section 8: Cousin Prime State Theorem -/


/-! ## Section 9: Mod-6 Automaton Structural Properties -/




/-! ## Section 10: Gap Parity -/

/-
**Gap Parity**: Gaps between primes > 2 are even.
-/


/-! ## Section 11: No Consecutive Equal Gaps -/



/-! ## Section 12: State Determination -/


/-! ## Section 13: Falsifiable Conjecture

**Gap AP Bound Conjecture**: For any even g > 0, consecutive equal gaps
of value g among primes > g have bounded run length.

Computational test: For g = 6, search for 5 consecutive primes each
differing by exactly 6 among primes up to 10^10. -/


end PrimeGapAutomaton



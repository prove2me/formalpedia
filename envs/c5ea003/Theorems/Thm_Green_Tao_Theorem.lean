-- Prove2me | Theorems.Thm_Green_Tao_Theorem
-- name    : Green_Tao_Theorem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-06-25T18:46:16.770453+00:00
-- url     : https://prove2.me/theorems/5aa0d1bd-1573-4b2b-9ff2-1a4fc1243dfd
-- statement:
--   **Green–Tao theorem.** The primes contain arbitrarily long arithmetic progressions: for every $N$ there is a set of primes that forms an arithmetic progression of cardinality at least $N$. (Proved by Green and Tao, 2004; statement following the DeepMind formal-conjectures library, Erdős problem 219.)
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/219.lean

import Mathlib

def IsAPOfLengthWithDM (s : Set ℕ) (l : ℕ∞) (a d : ℕ) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < l)}

def IsAPOfLengthDM (s : Set ℕ) (l : ℕ∞) : Prop := ∃ a d : ℕ, IsAPOfLengthWithDM s l a d

def primeArithmeticProgressionsDM : Set (Set ℕ) :=
  {s | (∀ p ∈ s, p.Prime) ∧ ∃ l > (0 : ℕ∞), IsAPOfLengthDM s l}

theorem Green_Tao_Theorem :
    ∀ N : ℕ, ∃ s ∈ primeArithmeticProgressionsDM, (N : ℕ∞) ≤ ENat.card s := by sorry

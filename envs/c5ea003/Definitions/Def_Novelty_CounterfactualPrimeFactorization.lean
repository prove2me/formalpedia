-- Prove2me | Definitions.Def_Novelty_CounterfactualPrimeFactorization
-- name    : Novelty_CounterfactualPrimeFactorization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:09:59.530522+00:00
-- url     : https://prove2.me/theorems/1ead4d27-325c-425d-b8a2-ed670c64bd8f
-- title:
--   Aether Catalog definitions — Novelty_CounterfactualPrimeFactorization
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CounterfactualPrimeFactorization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CounterfactualPrimeFactorization.lean by skeleton subtraction
import Mathlib

namespace CounterfactualPrimeFactorization

/-- The Hilbert multiplicative universe consists of naturals congruent to `1` modulo `4`. -/
def InHilbertMonoid (n : ℕ) : Prop := n % 4 = 1

instance : DecidablePred InHilbertMonoid := fun n => by
  unfold InHilbertMonoid
  infer_instance

/-- A Hilbert prime is a nonunit that has no nontrivial factorization within the
Hilbert multiplicative universe. -/
def HilbertPrime (n : ℕ) : Prop :=
  2 ≤ n ∧ InHilbertMonoid n ∧
    ∀ a b : ℕ, InHilbertMonoid a → InHilbertMonoid b → a * b = n → a = 1 ∨ b = 1








end CounterfactualPrimeFactorization



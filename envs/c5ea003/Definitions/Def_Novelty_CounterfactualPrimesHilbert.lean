-- Prove2me | Definitions.Def_Novelty_CounterfactualPrimesHilbert
-- name    : Novelty_CounterfactualPrimesHilbert
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:00.315247+00:00
-- url     : https://prove2.me/theorems/67eab276-fae0-4624-a6f7-8a29e28976fd
-- title:
--   Aether Catalog definitions — Novelty_CounterfactualPrimesHilbert
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CounterfactualPrimesHilbert`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CounterfactualPrimesHilbert.lean by skeleton subtraction
import Mathlib

/-!
# Counterfactual Number Theory: a Hilbert-type prime universe

What survives if the primes of arithmetic are replaced by the *irreducible*
elements of a different multiplicative world?  We study the classical
**Hilbert monoid**

  `H = { n : ℕ | n ≡ 1 (mod 4) } = {1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 41, 45, 49, …}`,

a multiplicatively closed subset of the naturals.  Its "primes" are the
`H`-irreducible elements — members of `H` that admit no nontrivial factorization
*inside* `H`.  This is a faithful toy model of a counterfactual number theory:
the ambient arithmetic is unchanged, but the notion of *which numbers are prime*
is deformed by only remembering the residue class `1 (mod 4)`.

The file separates the phenomena that **survive** this deformation from the one
that **collapses**:

* **Multiplicative structure survives** (`inH_one`, `inH_mul`): `H` is a submonoid
  of `(ℕ, ·)`.
* **Dirichlet-type infinitude survives** (`infinite_Hirr`): there are infinitely
  many `H`-irreducibles, obtained from the rational primes `p ≡ 1 (mod 4)`.
* **Unique factorization collapses** (`factorization_not_unique`): the number
  `441` has two genuinely different factorizations into `H`-irreducibles,
  `441 = 9 · 49 = 21 · 21`, with `9, 21, 49` all `H`-irreducible.

The collapse is the point: infinitude of primes and the multiplicative skeleton
are robust features that do not depend on the fine structure of the primes, while
unique factorization is fragile and depends essentially on it.

-- !-- Lab Notes -- !--
-- Hypothesis: replacing the primes by the irreducibles of the arithmetic
--   progression `1 (mod 4)` should preserve "coarse" multiplicative statements
--   (closure, infinitude of primes) while destroying "fine" ones
--   (unique factorization).
-- Experiment: formalize `H = {n ≡ 1 mod 4}`, its irreducibles `Hirr`, and test
--   each statement.  `9, 21, 49` are H-irreducible because their only proper
--   rational factors (`3, 7`) fall in the class `3 (mod 4)` and leave `H`.
--   `441 = 9·49 = 21·21` then exhibits two distinct irreducible factorizations.
-- Analysis: closure is a one-line residue computation; infinitude of
--   H-irreducibles reduces to Dirichlet's theorem for the progression
--   `1 (mod 4)` (the primes there are automatically H-irreducible); the failure
--   of unique factorization is a genuine structural obstruction, not an artifact
--   of small numbers.
-- Critique: `Hirr` must quantify over factorizations *inside* `H` (not over all
--   of `ℕ`), otherwise every composite would look reducible and the model would
--   be vacuous.  The multiset inequality `{9,49} ≠ {21,21}` certifies the two
--   factorizations are genuinely different, not a reordering.
-- Synthesis: "which primes" is a fragile datum; unique factorization is the first
--   casualty of deforming it, while Dirichlet infinitude and multiplicative
--   closure are robust.
-- !-- End Lab Notes -- !--
-/

namespace CounterfactualPrimes

/-- The **Hilbert monoid**: natural numbers congruent to `1` modulo `4`.
These are the "numbers" of our counterfactual arithmetic. -/
def inH (n : ℕ) : Prop := n % 4 = 1

instance : DecidablePred inH := fun n => by unfold inH; infer_instance

/-- An element is **`H`-irreducible** (a counterfactual prime) when it is a
non-unit member of `H` whose only factorizations *within `H`* are trivial. -/
def Hirr (n : ℕ) : Prop :=
  2 ≤ n ∧ inH n ∧ ∀ a b : ℕ, inH a → inH b → a * b = n → a = 1 ∨ b = 1









end CounterfactualPrimes



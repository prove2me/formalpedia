-- Prove2me | Definitions.Def_Applications_PoissonPairEvidence
-- name    : Applications_PoissonPairEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:27.013455+00:00
-- url     : https://prove2.me/theorems/3deccd1b-d3d3-4289-ac1e-3fd8e2e7af24
-- title:
--   Aether Catalog definitions — Applications_PoissonPairEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PoissonPairEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PoissonPairEvidence.lean by skeleton subtraction
import Mathlib
/-
# Machine-checked computational evidence for the classification of Poisson pairs

This is the *evidence* companion to `Catalog.Applications.PoissonSummationConverse`.  It is
deliberately elementary: the substantive theorems live in the other files, and nothing here
is used by them.

`FourierFA.isPoissonPair_iff_rectangle` predicts that, for a nonempty `S`, the pair `(S, T)`
satisfies Poisson summation exactly when the `S × T` block of the character table is
identically `1` and `|S| * |T| = |G|`; and `FourierFA.card_poissonPairs` predicts that the
number of such pairs is the number of subgroups.  For `G = ℤ/n` the characters are
`ψ_k(x) = e^{2πikx/n}`, so `ψ_k(x) = 1 ⟺ n ∣ kx`: the whole classification becomes the
integer condition below, and the predicted count is the number of divisors of `n`.

`rectCount n` brute-forces all `2^n * 2^n` pairs of subsets of `ℤ/n`.  The values below are
checked by the kernel (`decide`), not merely evaluated, and they agree with `σ₀(n)`:

  n        1  2  3  4  5  6
  rectCount 1  2  2  3  2  4
  σ₀(n)     1  2  2  3  2  4
-/


open Finset

namespace FourierFA

/-- The number of pairs of subsets `(S, T)` of `ℤ/n` whose character-table block is
identically one (in the exponent model `n ∣ k * x`) and whose area is exactly `n`. -/
def rectCount (n : ℕ) : ℕ :=
  (((univ : Finset (Finset (Fin n))) ×ˢ (univ : Finset (Finset (Fin n)))).filter
    (fun p => (∀ x ∈ p.1, ∀ k ∈ p.2, (x.val * k.val) % n = 0) ∧
      p.1.card * p.2.card = n)).card







end FourierFA



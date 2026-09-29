-- Prove2me | Definitions.Def_MachineLearning_FreeWitnessTraceLemma
-- name    : MachineLearning_FreeWitnessTraceLemma
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T15:17:37.348771+00:00
-- url     : https://prove2.me/theorems/7e0404c5-4b1d-4be4-b4a6-88a65959782e
-- title:
--   Aether Catalog definitions — MachineLearning_FreeWitnessTraceLemma
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.FreeWitnessTraceLemma`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/FreeWitnessTraceLemma.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Definitions.Def_MachineLearning_HalfPlaneSemiprime

/-!
# The CRT-multiplicative free-witness classification: the trace lemma

This file formalises the *abstract skeleton* of the free-witness classification of
`16_FreeWitness_Classification.md`.  The informal claim is:

> a counting aggregate over a CRT-separable domain whose local weights are
> non-polynomial and CRT-multiplicative is a "free witness": it determines the
> factorisation of a semiprime, and it is not a polynomial function of the modulus.

Both halves of that claim are made precise and proved here, in the only regime where
the claim has content, namely semiprimes `N = p q`:

* `SemiprimeWitness` — a value function `W : ℕ → ℤ` on moduli together with a *local
  weight* `w : ℕ → ℤ`, such that `W (p q) = w p * w q` for distinct odd primes.
  This is the "CRT-multiplicative" hypothesis, stripped of any particular model.

* `SemiprimeWitness.powerSum_recovery` — **the trace lemma in its general form.**
  If the local weight has the *power shape* `w x = x ^ k + c` with `c ≠ 0`, then
  `c * (p ^ k + q ^ k) = W (p q) - (p q) ^ k - c ^ 2`.
  The witness value therefore hands over one factor-secret coordinate, the power sum
  `p ^ k + q ^ k`, and nothing else is needed.

* `SemiprimeWitness.trace_recovery` — the case `k = 1`: the *trace* `s = p + q` is
  read off from `W (p q)`.

* `vieta_roots`, `pair_determined_of_sum_prod` — once the trace is known both factors
  are pinned down: they are the roots of `X ^ 2 - s X + N`, and no other pair of
  positive integers has that sum and that product.  This is the "information content
  of every witness is one factor-secret coordinate" statement.

* `not_polynomial_of_not_dvd` — **the polynomial barrier, in sharp form.**  For an
  integer polynomial `P` one always has `a - b ∣ P(a) - P(b)`.  So a single pair of
  moduli `N₁, N₂` with `N₁ - N₂ ∤ W N₁ - W N₂` *proves* that `W` agrees with no
  integer polynomial on any set containing `N₁, N₂`.  This is exactly the proof
  direction sketched in §5 of the paper (a congruence separation), and it is
  unconditional.

* `circleWitness`, `circleCount_not_polynomial` — the classification applied to the
  catalog's modular circle count `HalfPlane.circleCount`.  The local weight is
  `p - χ_p(-1)`; for Blum primes it has power shape `x + 1`, so the trace lemma
  reproves (and generalises) `HalfPlane.sum_of_primes_from_circleCount`, and the
  divisibility criterion shows `C` is not a polynomial in `N`.

Nothing here assumes anything about *how* `W` is computed; the classification is a
statement about the shape of the local weight only.
-/

namespace FreeWitness

open Finset

/-! ## The abstract witness -/

/-- A **CRT-multiplicative semiprime witness**: a global value `W N` attached to each
modulus, which on a product of two distinct odd primes factors as a product of local
weights `w p * w q`.  This is the abstract form of the "CRT decomposition + local
weight" layer of the free-witness mechanism. -/
structure SemiprimeWitness where
  /-- the aggregate, as a function of the modulus -/
  W : ℕ → ℤ
  /-- the local weight, a function of a single prime -/
  w : ℕ → ℤ
  /-- CRT-multiplicativity on semiprimes -/
  factorizes : ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q →
    W (p * q) = w p * w q

namespace SemiprimeWitness

variable (F : SemiprimeWitness)





end SemiprimeWitness

/-! ## From the trace to the factors -/



/-! ## The polynomial barrier -/



/-! ## Instance: the modular circle count (CIRC) -/

open HalfPlane

/-- The catalog's modular circle count `C(N) = #{(x,y) : x² + y² ≡ 1 mod N}`, packaged as
a CRT-multiplicative semiprime witness with local weight `p - χ_p(-1)`. -/
def circleWitness : SemiprimeWitness where
  W N := (circleCount N : ℤ)
  w p := if p % 4 = 1 then (p : ℤ) - 1 else (p : ℤ) + 1
  factorizes := by
    intro p q hp hq hp2 hq2 hpq
    have h := circleCount_semiprime hp hq hp2 hq2 hpq
    have hp1 : 1 ≤ p := hp.one_lt.le.trans' (by norm_num)
    have hq1 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
    rw [h]
    by_cases h4p : p % 4 = 1 <;> by_cases h4q : q % 4 = 1 <;>
      simp only [h4p, h4q, if_true, if_false] <;> push_cast [Nat.cast_sub hp1, Nat.cast_sub hq1] <;>
      ring





/-! ### Lab notes (cycle 1)

```
N = p·q   C(N)   local weights        trace   C(N) - N - 1
21 = 3·7    32   (3+1)(7+1)             10        10   ✓
33 = 3·11   48   (3+1)(11+1)            14        14   ✓
57 = 3·19   80   (3+1)(19+1)            22        22   ✓
15 = 3·5    16   (3+1)(5-1)      (5 ≡ 1 mod 4: not a Blum pair)
```
Difference test for the polynomial barrier:
`21 - 15 = 6`, `C(21) - C(15) = 16`, and `6 ∤ 16`.
-/

end FreeWitness



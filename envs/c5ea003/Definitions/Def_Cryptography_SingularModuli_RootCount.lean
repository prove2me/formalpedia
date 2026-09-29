-- Prove2me | Definitions.Def_Cryptography_SingularModuli_RootCount
-- name    : Cryptography_SingularModuli_RootCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:34:41.109157+00:00
-- url     : https://prove2.me/theorems/9a95de3a-17ab-4980-b870-e21a277ba74b
-- title:
--   Aether Catalog definitions — Cryptography_SingularModuli_RootCount
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SingularModuli.RootCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SingularModuli/RootCount.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion

/-!
# Singular Moduli Factoring, Step 2: exactly how many evaluation points work

Fix a monic `H ∈ ℤ[X]` (think: the Hilbert class polynomial `H_D`, which is
monic of degree the class number `h(D)`) and a semiprime `N = p q`.  By the
criterion of `GcdCriterion.lean`, an evaluation point `j₀` succeeds iff `j₀` is a
root of `H` mod exactly one of `p`, `q`.  Since that condition only depends on
`j₀ mod p` and `j₀ mod q`, the Chinese remainder theorem turns the count of
successful `j₀ ∈ [0, N)` into a product count.

Main results:

* `card_filter_xor_prod`   — the pure product-counting identity;
* `card_range_filter_crt`  — CRT transfer from `[0, pq)` to `ZMod p × ZMod q`;
* `successCount_eq`        — **the exact success count**
  `S = r_p (q - r_q) + (p - r_p) r_q`, where `r_m` is the number of roots of
  `H` mod `m`;
* `rootCount_le_natDegree` — `r_m ≤ deg H` (`= h` for a Hilbert class polynomial);
* `successCount_le`        — hence `S ≤ h (p + q)`: only an `O(h(p+q))`-sized
  subset of the `pq` residues is useful.

The last bound is the combinatorial source of the `√N` barrier proved in
`SqrtBarrier.lean`.
-/

namespace SingularModuli

open Polynomial Finset FactoringBarriers

/-- The reduction of the integer polynomial `H` modulo `m`. -/
noncomputable def redMod (H : Polynomial ℤ) (m : ℕ) : Polynomial (ZMod m) :=
  H.map (Int.castRingHom (ZMod m))

/-- The set of roots of `H` modulo `m`. -/
noncomputable def rootFinset (H : Polynomial ℤ) (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.filter (fun x => (redMod H m).eval x = 0)

/-- The number of roots of `H` modulo `m`.  For a Hilbert class polynomial `H_D`
and a prime `p` for which `D` is a square mod `p`, this is the class number `h`. -/
noncomputable def rootCount (H : Polynomial ℤ) (m : ℕ) [NeZero m] : ℕ :=
  (rootFinset H m).card



/-! ## The product count -/


/-! ## Chinese remainder transfer -/


/-! ## The exact success count -/

open scoped Classical in
/-- The set of evaluation points in `[0, N)` at which the gcd step succeeds. -/
noncomputable def successSet (H : Polynomial ℤ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun j => NontrivialDivisor N (evalGcd H (j : ℤ) N))

open scoped Classical in
/-- The number of useful evaluation points modulo `N`. -/
noncomputable def successCount (H : Polynomial ℤ) (N : ℕ) : ℕ := (successSet H N).card



end SingularModuli



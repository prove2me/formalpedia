-- Prove2me | Theorems.Thm_SingularModuli_successCount_le
-- name    : SingularModuli.successCount_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:05:42.258983+00:00
-- url     : https://prove2.me/theorems/a45251d7-2d72-4b84-b1d4-731b621cebba
-- title:
--   The useful set is tiny.
-- statement:
--   **The useful set is tiny.** For monic `H` of degree `h`, at most `h (p + q)`
--   of the `pq` residues are useful evaluation points.
--
--   ```lean
--   theorem SingularModuli.successCount_le{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
--       {H : Polynomial ℤ} (hH : H.Monic) :
--       successCount H (p * q) ≤ H.natDegree * (p + q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SingularModuli/RootCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SingularModuli/RootCount.lean#L208

-- Thm stub generated from Cryptography/SingularModuli/RootCount.lean
import Mathlib
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount

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

open SingularModuli

open Polynomial Finset FactoringBarriers






/-! ## The product count -/


/-! ## Chinese remainder transfer -/


/-! ## The exact success count -/

theorem SingularModuli.successCount_le{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {H : Polynomial ℤ} (hH : H.Monic) :
    successCount H (p * q) ≤ H.natDegree * (p + q) := by sorry

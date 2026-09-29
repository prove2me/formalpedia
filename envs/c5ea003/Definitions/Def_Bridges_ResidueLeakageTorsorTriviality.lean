-- Prove2me | Definitions.Def_Bridges_ResidueLeakageTorsorTriviality
-- name    : Bridges_ResidueLeakageTorsorTriviality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:32.869101+00:00
-- url     : https://prove2.me/theorems/cf5a5853-2eb2-4eee-a770-993ed62486d9
-- title:
--   Aether Catalog definitions — Bridges_ResidueLeakageTorsorTriviality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ResidueLeakageTorsorTriviality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ResidueLeakageTorsorTriviality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
/-
# The consistent factor-fingerprint set is a trivial torsor (conjecture C5, closed)

Eighth file of the residue-leakage thread.  The previous files show that the QR
fingerprint prunes nothing (`dirichlet_no_pruning`), that all `2^K` patterns
occur (`qrFingerprint_pattern_surjective`), and that consistency of a pair of
primes with the observation is *exactly* the symmetric relation
`(a|q) = (a|N₀)·(a|p)` (`consistent_iff_product_constraint`).

Conjecture C5 of `FUTURE_DIRECTIONS.md` asked for the structural reformulation:
the "factorisation fibre"

`Φ(N₀) = { (F_A(p), F_A(q)) : p, q prime, F_A(p·q) = F_A(N₀) }`

should be a *trivial torsor* under the anti-diagonal
`Δ⁻ = { (w, w) : w ∈ {±1}^K }`, and this triviality should be equivalent to the
no-pruning statement.  This file proves it:

* `consistentPairs_eq` — the fibre is precisely the graph of the translation
  `u ↦ F_A(N₀) · u`, i.e. a coset of `Δ⁻` in `{±1}^K × {±1}^K`;
* `consistentPairs_simply_transitive` — `Δ⁻` acts *simply transitively* on the
  fibre (existence **and** uniqueness of the connecting sign vector): the fibre
  has trivial monodromy, so it is a trivial `Δ⁻`-torsor;
* `consistentPairs_fst_eq` — the fibre projects **onto** all of `{±1}^K` in the
  first coordinate, which is the no-pruning theorem in torsor form;
* `consistentPairs_ncard` — the fibre has exactly `2^K` elements, i.e. the
  residue channel leaves exactly the full `K` free bits of `F_A(p)`.

Everything is proved for an arbitrary duplicate-free list `A` of probe primes.
-/


namespace Bridges.ResidueLeakage

/-! ## Pointwise multiplication of sign vectors -/

/-- Pointwise product of two sign vectors; the group law of `{±1}^K`. -/
def signMul (u v : List ℤ) : List ℤ := List.zipWith (· * ·) u v



/-! ## Bookkeeping: symbols of a prime outside the probe set -/



/-! ## The factorisation fibre -/

/-- The **factorisation fibre** of the observation `F_A(N₀)`: all pairs of
fingerprints `(F_A(p), F_A(q))` of primes `p, q` outside the probe set whose
product has the observed fingerprint. -/
def consistentPairs (A : List ℕ) (N₀ : ℕ) : Set (List ℤ × List ℤ) :=
  {uv | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ∉ A ∧ q ∉ A ∧
      qrFingerprint A p = uv.1 ∧ qrFingerprint A q = uv.2 ∧
      qrFingerprint A (p * q) = qrFingerprint A N₀}


/-! ## Trivial monodromy: the anti-diagonal acts simply transitively -/


/-! ## Torsor form of the no-pruning theorem, and the exact size of the fibre -/




end Bridges.ResidueLeakage



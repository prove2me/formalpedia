-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_consistentPairs_eq
-- name    : Bridges.ResidueLeakage.consistentPairs_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:30.672859+00:00
-- url     : https://prove2.me/theorems/d480d83f-7b07-43dd-8209-71d5e05fe7e6
-- title:
--   The fibre is a coset of the anti-diagonal.
-- statement:
--   **The fibre is a coset of the anti-diagonal.**  A pair of sign vectors is
--   realised by a consistent pair of primes exactly when the second coordinate is
--   the pointwise product of the observation with the first.  In particular the
--   first coordinate is completely free: the channel carries no information about
--   the individual factor.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.consistentPairs_eq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime) (hnd : A.Nodup)
--       {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) :
--       consistentPairs A N₀ =
--         {uv : List ℤ × List ℤ | uv.1 ∈ signVectors A.length ∧
--           uv.2 = signMul (qrFingerprint A N₀) uv.1} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakageTorsorTriviality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakageTorsorTriviality.lean#L89

-- Thm stub generated from Bridges/ResidueLeakageTorsorTriviality.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Definitions.Def_Bridges_ResidueLeakageTorsorTriviality
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


open Bridges.ResidueLeakage

/-! ## Pointwise multiplication of sign vectors -/




/-! ## Bookkeeping: symbols of a prime outside the probe set -/



/-! ## The factorisation fibre -/

theorem Bridges.ResidueLeakage.consistentPairs_eq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime) (hnd : A.Nodup)
    {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) :
    consistentPairs A N₀ =
      {uv : List ℤ × List ℤ | uv.1 ∈ signVectors A.length ∧
        uv.2 = signMul (qrFingerprint A N₀) uv.1} := by sorry

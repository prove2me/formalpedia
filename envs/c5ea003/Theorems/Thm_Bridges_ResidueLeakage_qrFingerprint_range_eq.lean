-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_range_eq
-- name    : Bridges.ResidueLeakage.qrFingerprint_range_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:32:48.020046+00:00
-- url     : https://prove2.me/theorems/a39e9c54-2de9-40a6-87fc-c586f73fbeca
-- title:
--   The range of the QR fingerprint on primes is everything.
-- statement:
--   **The range of the QR fingerprint on primes is everything.**  For distinct
--   probe primes `A`, the fingerprints of the primes `q ∉ A` are exactly the
--   `±1`-vectors of length `|A|`; there are `2^|A|` of them and each occurs.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.qrFingerprint_range_eq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       (hnd : A.Nodup) :
--       {v : List ℤ | ∃ q : ℕ, q.Prime ∧ q ∉ A ∧ qrFingerprint A q = v}
--         = {v : List ℤ | v.length = A.length ∧ ∀ x ∈ v, x = 1 ∨ x = -1} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakagePatternSurjectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakagePatternSurjectivity.lean#L305

-- Thm stub generated from Bridges/ResidueLeakagePatternSurjectivity.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
/-
# Pattern surjectivity of the QR fingerprint, and the failure of individual pinning

Companion file to `Bridges.ResidueLeakageDirichletNoPruning`.

Where the no-pruning theorem shows that the cheap residue channel cannot *remove*
any candidate prime, this file shows the complementary, constructive fact: the
fingerprint map is **surjective onto all `2^K` sign patterns**, already on primes.
The proof is a genuine cross-domain bridge:

* Chinese remainder theorem (`existsCRT`) to build the residue class,
* quadratic reciprocity + the supplementary law at `2` (`jacobiSym.at_two`),
* existence of a quadratic nonresidue in a finite field
  (`FiniteField.exists_nonsquare`),
* Dirichlet's theorem (imported through `infinite_primes_jacobi_eq`).

Main results:

* `exists_prime_jacobi_pattern` — every prescribed sign pattern on a set of
  distinct odd probe primes, together with a prescribed value at `2`, is
  realised by infinitely many primes.
* `qrFingerprint_pattern_surjective` — the same for an arbitrary list of
  distinct probe primes (the prime `2` allowed): all `2^K` fingerprints occur.
* `no_individual_pinning` — for any observed `F_A(N₀)` and any probe prime `a₀`,
  there are consistent factorisations `p₁q₁` and `p₂q₂` of the *same*
  fingerprint with `(a₀|p₁) = 1` and `(a₀|p₂) = -1`: the data pins down no
  individual symbol of a factor, only the symmetric products.
-/


open Bridges.ResidueLeakage

/-! ## A Chinese remainder theorem for lists of moduli -/


/-! ## A quadratic nonresidue witness -/



/-! ## Building a modulus with a prescribed symbol pattern -/



/-! ## Pattern surjectivity on primes -/



/-! ## No individual pinning -/


/-! ## The exact range of the fingerprint -/

theorem Bridges.ResidueLeakage.qrFingerprint_range_eq{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (hnd : A.Nodup) :
    {v : List ℤ | ∃ q : ℕ, q.Prime ∧ q ∉ A ∧ qrFingerprint A q = v}
      = {v : List ℤ | v.length = A.length ∧ ∀ x ∈ v, x = 1 ∨ x = -1} := by sorry

-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_exists_map_eq_of_nodup
-- name    : Bridges.ResidueLeakage.exists_map_eq_of_nodup
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:30.643168+00:00
-- url     : https://prove2.me/theorems/c4014d80-dc7e-426f-a4c8-c3019d7deb87
-- title:
--   On a duplicate-free list any target list of the right length is the image of
-- statement:
--   On a duplicate-free list any target list of the right length is the image of
--   some function.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.exists_map_eq_of_nodup: ∀ (A : List ℕ), A.Nodup → ∀ v : List ℤ,
--       v.length = A.length → ∃ ε : ℕ → ℤ, A.map ε = v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakagePatternSurjectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakagePatternSurjectivity.lean#L282

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

theorem Bridges.ResidueLeakage.exists_map_eq_of_nodup: ∀ (A : List ℕ), A.Nodup → ∀ v : List ℤ,
    v.length = A.length → ∃ ε : ℕ → ℤ, A.map ε = v := by sorry

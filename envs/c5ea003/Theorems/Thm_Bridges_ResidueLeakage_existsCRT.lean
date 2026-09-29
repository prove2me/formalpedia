-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_existsCRT
-- name    : Bridges.ResidueLeakage.existsCRT
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:42.417236+00:00
-- url     : https://prove2.me/theorems/ffc246fb-3ce6-4128-80c4-ff0a6c56be00
-- title:
--   Chinese remainder theorem for a list of pairwise coprime moduli:
-- statement:
--   Chinese remainder theorem for a list of pairwise coprime moduli:
--   prescribed residues `f x` mod `x` can be realised simultaneously.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.existsCRT: ∀ (L : List ℕ), L.Pairwise Nat.Coprime → ∀ f : ℕ → ℕ,
--       ∃ m : ℕ, ∀ x ∈ L, m ≡ f x [MOD x] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakagePatternSurjectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakagePatternSurjectivity.lean#L36

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

theorem Bridges.ResidueLeakage.existsCRT: ∀ (L : List ℕ), L.Pairwise Nat.Coprime → ∀ f : ℕ → ℕ,
    ∃ m : ℕ, ∀ x ∈ L, m ≡ f x [MOD x] := by sorry

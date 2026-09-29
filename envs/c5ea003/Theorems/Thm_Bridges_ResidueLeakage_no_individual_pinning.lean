-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_no_individual_pinning
-- name    : Bridges.ResidueLeakage.no_individual_pinning
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:34:35.545911+00:00
-- url     : https://prove2.me/theorems/b4b8b0f1-6a9c-482b-af28-022a526558c2
-- title:
--   No individual pinning.
-- statement:
--   **No individual pinning.**  Fix probe primes `A`, an observed fingerprint
--   `F_A(N₀)`, and a probe prime `a₀ ∈ A`.  Then there are two semiprimes
--   `p₁ * q₁` and `p₂ * q₂` with *the same* fingerprint as `N₀` whose first factors
--   have opposite symbols at `a₀`.  Hence the residue data determines no individual
--   symbol `(a₀ | p)` of a factor — only the symmetric products `(a₀|p)(a₀|q)`,
--   which are already read off from `N₀` itself.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.no_individual_pinning{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a)
--       {a₀ : ℕ} (ha₀ : a₀ ∈ A) :
--       ∃ p₁ q₁ p₂ q₂ : ℕ,
--         p₁.Prime ∧ q₁.Prime ∧ p₂.Prime ∧ q₂.Prime ∧
--         qrFingerprint A (p₁ * q₁) = qrFingerprint A N₀ ∧
--         qrFingerprint A (p₂ * q₂) = qrFingerprint A N₀ ∧
--         jacobiSym (a₀ : ℤ) p₁ = 1 ∧ jacobiSym (a₀ : ℤ) p₂ = -1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakagePatternSurjectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakagePatternSurjectivity.lean#L236

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

theorem Bridges.ResidueLeakage.no_individual_pinning{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a)
    {a₀ : ℕ} (ha₀ : a₀ ∈ A) :
    ∃ p₁ q₁ p₂ q₂ : ℕ,
      p₁.Prime ∧ q₁.Prime ∧ p₂.Prime ∧ q₂.Prime ∧
      qrFingerprint A (p₁ * q₁) = qrFingerprint A N₀ ∧
      qrFingerprint A (p₂ * q₂) = qrFingerprint A N₀ ∧
      jacobiSym (a₀ : ℤ) p₁ = 1 ∧ jacobiSym (a₀ : ℤ) p₂ = -1 := by sorry

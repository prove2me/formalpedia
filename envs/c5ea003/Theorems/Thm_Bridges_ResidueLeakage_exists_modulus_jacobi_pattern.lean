-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_exists_modulus_jacobi_pattern
-- name    : Bridges.ResidueLeakage.exists_modulus_jacobi_pattern
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:53.242477+00:00
-- url     : https://prove2.me/theorems/001d0493-29d8-4f86-8cf1-211a84e1daf7
-- title:
--   Existence of a modulus with any prescribed pattern.
-- statement:
--   **Existence of a modulus with any prescribed pattern.**
--
--   ```lean
--   theorem Bridges.ResidueLeakage.exists_modulus_jacobi_pattern{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       (h2 : ∀ a ∈ A, a ≠ 2) (hnd : A.Nodup) {e₂ : ℤ} (he₂ : e₂ = 1 ∨ e₂ = -1)
--       {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
--       ∃ m : ℕ, Odd m ∧ Nat.Coprime m 2 ∧ (∀ a ∈ A, Nat.Coprime m a) ∧
--         jacobiSym 2 m = e₂ ∧ ∀ a ∈ A, jacobiSym (a : ℤ) m = ε a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakagePatternSurjectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakagePatternSurjectivity.lean#L82

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

theorem Bridges.ResidueLeakage.exists_modulus_jacobi_pattern{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (h2 : ∀ a ∈ A, a ≠ 2) (hnd : A.Nodup) {e₂ : ℤ} (he₂ : e₂ = 1 ∨ e₂ = -1)
    {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
    ∃ m : ℕ, Odd m ∧ Nat.Coprime m 2 ∧ (∀ a ∈ A, Nat.Coprime m a) ∧
      jacobiSym 2 m = e₂ ∧ ∀ a ∈ A, jacobiSym (a : ℤ) m = ε a := by sorry

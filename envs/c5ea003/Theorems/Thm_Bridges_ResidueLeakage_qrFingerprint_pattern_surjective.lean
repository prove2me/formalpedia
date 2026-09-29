-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_pattern_surjective
-- name    : Bridges.ResidueLeakage.qrFingerprint_pattern_surjective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:32:20.647413+00:00
-- url     : https://prove2.me/theorems/db770af6-2ab2-491d-9bf7-34b149ef1f10
-- title:
--   Fingerprint surjectivity.
-- statement:
--   **Fingerprint surjectivity.**  For any list `A` of distinct primes (the
--   prime `2` allowed) and any `±1`-pattern, infinitely many primes realise that
--   fingerprint.  With `A` the first `K` primes this gives all `2^K` patterns.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.qrFingerprint_pattern_surjective{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
--       (hnd : A.Nodup) {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
--       {q : ℕ | q.Prime ∧ Odd q ∧ qrFingerprint A q = A.map ε}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ResidueLeakagePatternSurjectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ResidueLeakagePatternSurjectivity.lean#L200

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

theorem Bridges.ResidueLeakage.qrFingerprint_pattern_surjective{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (hnd : A.Nodup) {ε : ℕ → ℤ} (hε : ∀ a ∈ A, ε a = 1 ∨ ε a = -1) :
    {q : ℕ | q.Prime ∧ Odd q ∧ qrFingerprint A q = A.map ε}.Infinite := by sorry

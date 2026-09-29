-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_abelian_channel_no_pruning
-- name    : Bridges.ResidueLeakage.abelian_channel_no_pruning
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:03.562004+00:00
-- url     : https://prove2.me/theorems/5bbc703e-86c4-4ea3-b909-15cef4693a87
-- title:
--   Abelian no-pruning.
-- statement:
--   **Abelian no-pruning.**  For any finite family of Dirichlet characters of a
--   fixed modulus `M`, any target `N₀` coprime to `M`, and any candidate `p`
--   coprime to `M` (primality of `p` is not even needed), there are infinitely many
--   primes `q` such that `p·q` has exactly
--   the same character fingerprint as `N₀`.
--
--   No abelian residue channel of bounded conductor can eliminate a single candidate
--   prime factor.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.abelian_channel_no_pruning{R : Type*} [CommMonoidWithZero R] {M : ℕ}
--       [NeZero M] (X : List (DirichletCharacter R M)) {N₀ p : ℕ}
--       (hN₀ : Nat.Coprime N₀ M) (hpM : Nat.Coprime p M) :
--       {q : ℕ | q.Prime ∧ charFingerprint X (p * q) = charFingerprint X N₀}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AbelianChannelNoPruning.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AbelianChannelNoPruning.lean#L30

-- Thm stub generated from Bridges/AbelianChannelNoPruning.lean
import Mathlib
import Definitions.Def_Bridges_AbelianChannelNoPruning
/-
# The abelian channel no-pruning theorem

Fifth file of the residue-leakage thread.  This closes conjecture **C3** of
`FUTURE_DIRECTIONS.md` for a fixed conductor: the Dirichlet no-pruning
phenomenon is not about quadratic residues at all.  It holds for *every* finite
family of Dirichlet characters of a fixed modulus — i.e. for every abelian
residue channel of bounded conductor, in any coefficient ring.

Given probes `χ₁,…,χ_K : DirichletCharacter R M` define the *character
fingerprint* `Φ(N) = [χ_i(N)]`.  For a target `N₀` coprime to `M` and any
candidate prime `p ∤ M`, put `q` in the class `N₀ · p⁻¹ (mod M)`: then
`χ_i(pq) = χ_i(p)·χ_i(N₀ p⁻¹) = χ_i(N₀)` for every `i`, and Dirichlet's theorem
supplies infinitely many primes in that class.

The quadratic case (`Bridges.ResidueLeakageDirichletNoPruning`) is the special
case where each `χ_i` is the Jacobi symbol `(a_i | ·)` of conductor `4a_i`; there
`p⁻¹ ≡ p` up to squares, which is why the compensating class was `N₀ · p`.
-/


open Bridges.ResidueLeakage

theorem Bridges.ResidueLeakage.abelian_channel_no_pruning{R : Type*} [CommMonoidWithZero R] {M : ℕ}
    [NeZero M] (X : List (DirichletCharacter R M)) {N₀ p : ℕ}
    (hN₀ : Nat.Coprime N₀ M) (hpM : Nat.Coprime p M) :
    {q : ℕ | q.Prime ∧ charFingerprint X (p * q) = charFingerprint X N₀}.Infinite := by sorry

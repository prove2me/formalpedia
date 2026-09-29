-- Prove2me | Theorems.Thm_Bridges_ResidueLeakage_jacobiSym_two_no_pruning
-- name    : Bridges.ResidueLeakage.jacobiSym_two_no_pruning
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:34:22.314865+00:00
-- url     : https://prove2.me/theorems/632a77a3-a729-4f18-8a63-df9032ef80af
-- title:
--   Instance of the general theorem for the mod-`8` quadratic character: the
-- statement:
--   Instance of the general theorem for the mod-`8` quadratic character: the
--   symbol `(2 | ·)` cannot prune either.  Here the general machinery reproduces a
--   case of `dirichlet_no_pruning` without any use of quadratic reciprocity.
--
--   ```lean
--   theorem Bridges.ResidueLeakage.jacobiSym_two_no_pruning{N₀ p : ℕ} (hN₀ : Odd N₀) (hp : Odd p) :
--       {q : ℕ | q.Prime ∧ jacobiSym 2 (p * q) = jacobiSym 2 N₀}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AbelianChannelNoPruning.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AbelianChannelNoPruning.lean#L79

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




/-! ## A quadratic instance: the supplementary symbol at `2` -/

theorem Bridges.ResidueLeakage.jacobiSym_two_no_pruning{N₀ p : ℕ} (hN₀ : Odd N₀) (hp : Odd p) :
    {q : ℕ | q.Prime ∧ jacobiSym 2 (p * q) = jacobiSym 2 N₀}.Infinite := by sorry

-- Prove2me | Definitions.Def_Bridges_AbelianChannelNoPruning
-- name    : Bridges_AbelianChannelNoPruning
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:09.793583+00:00
-- url     : https://prove2.me/theorems/384fd27e-93f9-42b9-838d-de386cbad07d
-- title:
--   Aether Catalog definitions — Bridges_AbelianChannelNoPruning
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AbelianChannelNoPruning`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AbelianChannelNoPruning.lean by skeleton subtraction
import Mathlib
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


namespace Bridges.ResidueLeakage

/-- The character fingerprint of `N` relative to a list of Dirichlet characters
of modulus `M`. -/
def charFingerprint {R : Type*} [CommMonoidWithZero R] {M : ℕ}
    (X : List (DirichletCharacter R M)) (N : ℕ) : List R :=
  X.map (fun χ => χ (N : ZMod M))



/-! ## A quadratic instance: the supplementary symbol at `2` -/



end Bridges.ResidueLeakage



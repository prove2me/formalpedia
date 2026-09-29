-- Prove2me | Theorems.Thm_TwoTreeClosure_gaussBattery_letterBlind
-- name    : TwoTreeClosure.gaussBattery_letterBlind
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:25:52.108764+00:00
-- url     : https://prove2.me/theorems/21b43049-6f25-4ae6-a88f-b26a087b80d0
-- title:
--   Even a whole finite battery of Gauss-sum probes, at arbitrarily many moduli,
-- statement:
--   Even a whole finite battery of Gauss-sum probes, at arbitrarily many moduli,
--   stays blind: the joint readout is still a function of `N mod (∏ moduli)`, and the
--   blindness family of `letterOf_blind_of_residue` was built for an arbitrary modulus.
--   Concretely, a battery indexed by a finite set of moduli all dividing `M` is blind.
--
--   ```lean
--   theorem TwoTreeClosure.gaussBattery_letterBlind(M : ℕ) (hM : 1 ≤ M) (s : Finset ℕ)
--       (hs : ∀ d ∈ s, d ∣ M ∧ 0 < d) (G : (ℕ → ℂ) → Letter) :
--       ¬ (∀ m n, IsNode m n → G (fun d => if d ∈ s then gaussSum d (hyp m n) else 0)
--           = letterOf m n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TwoTreeClosure/GaussDial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TwoTreeClosure/GaussDial.lean#L71

-- Thm stub generated from Bridges/TwoTreeClosure/GaussDial.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_GaussDial
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

/-!
# Gauss-sum magnitudes are residue dials, hence tree-blind

Strength (2) of the two-tree closure.  A *Gauss-sum probe* at modulus `M` reads

`G_M(N) = ∑_{x < M} exp(2πi x² N / M)`,

and derived probes read any function of `G_M(N)` (for instance its magnitude, its
argument, or a whole vector of such sums at several moduli).

`gaussSum_periodic` proves that `G_M` is invariant under `N ↦ N + M`, hence
`gaussSum_eq_mod` : `G_M(N) = G_M(N mod M)`.  So every Gauss-sum probe *is* a
residue dial, and `gaussProbe_letterBlind` transports the blindness theorem of
`Bridges.TwoTreeClosure.TreeCore` to it: no Gauss-sum probe at any modulus — in
particular none at the smooth modulus `720720` — can output the ascent letter of a
Berggren/Price node.
-/

open TwoTreeClosure

open Finset

theorem TwoTreeClosure.gaussBattery_letterBlind(M : ℕ) (hM : 1 ≤ M) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∣ M ∧ 0 < d) (G : (ℕ → ℂ) → Letter) :
    ¬ (∀ m n, IsNode m n → G (fun d => if d ∈ s then gaussSum d (hyp m n) else 0)
        = letterOf m n) := by sorry

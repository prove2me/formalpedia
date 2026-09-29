-- Prove2me | Theorems.Thm_TwoTreeClosure_gaussSum_periodic
-- name    : TwoTreeClosure.gaussSum_periodic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:25:40.253547+00:00
-- url     : https://prove2.me/theorems/c0d311cf-13f7-45e4-ab84-8d09f6e7fdb6
-- title:
--   Gauss sums are `M`-periodic in `N`.
-- statement:
--   **Gauss sums are `M`-periodic in `N`.**
--
--   ```lean
--   theorem TwoTreeClosure.gaussSum_periodic(M N k : ℕ) (hM : 0 < M) :
--       gaussSum M (N + k * M) = gaussSum M N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TwoTreeClosure/GaussDial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TwoTreeClosure/GaussDial.lean#L29

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

theorem TwoTreeClosure.gaussSum_periodic(M N k : ℕ) (hM : 0 < M) :
    gaussSum M (N + k * M) = gaussSum M N := by sorry

-- Prove2me | Definitions.Def_Bridges_TwoTreeClosure_GaussDial
-- name    : Bridges_TwoTreeClosure_GaussDial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:51.924294+00:00
-- url     : https://prove2.me/theorems/31de20f4-c1ef-464d-94ab-fa40f2d65695
-- title:
--   Aether Catalog definitions — Bridges_TwoTreeClosure_GaussDial
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TwoTreeClosure.GaussDial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TwoTreeClosure/GaussDial.lean by skeleton subtraction
import Mathlib
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

namespace TwoTreeClosure

open Finset

/-- The quadratic Gauss sum of `N` at modulus `M`. -/
noncomputable def gaussSum (M N : ℕ) : ℂ :=
  ∑ x ∈ range M, Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) ^ 2 * (N : ℂ)) / (M : ℂ))






end TwoTreeClosure



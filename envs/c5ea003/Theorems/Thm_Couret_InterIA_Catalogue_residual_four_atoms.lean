-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_residual_four_atoms
-- name    : Couret.InterIA.Catalogue.residual_four_atoms
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:30:56.32292+00:00
-- url     : https://prove2.me/theorems/608090ba-a9e0-4dcf-97f3-b9b6895ab70f
-- title:
--   residual four atoms
-- statement:
--   For every natural number $m$, a two-element finite subset $C⊆R=ℤ/(2m)ℤ$, and $a,b∈R$, there exist distinct $c,d∈R$ with $C=\{c,d\}$ such that $∑_{x∈C}e_{π(x)}+e_{π(a)}+e_{π(b)}=e_{π(c)}+e_{π(d)}+e_{π(a)}+e_{π(b)}$ in $ℤ[ℤ/mℤ]$, where $π$ is the canonical reduction map and $e_y$ has coefficient $1$ at $y$ and $0$ elsewhere. The case $m=0$, with both residue rings equal to $ℤ$, is included, and projected atoms may coincide.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientResidual.lean, lines 57–68; source file SHA-256 29c3ae2cbecdf646a84bc5ab6931803cdc7db5ad9705778c5cd73f60b149f4bb; theorem Couret.InterIA.Catalogue.residual_four_atoms

import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_L4Assembly_154a326d9c14

set_option autoImplicit false
namespace Couret.InterIA.Catalogue
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing
open Couret.InterIA.Projection

theorem residual_four_atoms (m : ℕ) (C : Finset (ZMod (2*m))) (hC : C.card=2)
    (a b : ZMod (2*m)) :
    ∃ c d : ZMod (2*m), c ≠ d ∧ C={c,d} ∧
      residual m C a b=A (projection m c)+A (projection m d)+A (projection m a)+A (projection m b) := by sorry










end Couret.InterIA.Catalogue

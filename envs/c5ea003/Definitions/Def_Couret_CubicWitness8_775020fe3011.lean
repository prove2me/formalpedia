-- Prove2me | Definitions.Def_Couret_CubicWitness8_775020fe3011
-- name    : Couret_CubicWitness8_775020fe3011
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:12:42.02486+00:00
-- url     : https://prove2.me/theorems/ddfca5b2-01c0-44ec-a9e6-1b1930a3332a
-- title:
--   Four concrete supports modulo eight
-- statement:
--   Defines four subsets of $\mathbb Z/8\mathbb Z$, indexed by $0,1,2,3$: $\{0,1,5,6\}$, $\{0,3,6,7\}$, $\{1,2,4,5\}$ and $\{2,3,4,7\}$. These are explicit witnesses for cubic-probe and fibre analysis.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicWitness8.lean; source file SHA-256 0cc66040496efdae6a0da5aaa1913b71bfc216fdce6455ba2090aafac04342a7

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CubicReconstruction_bc5d14805c7e

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

def witness8 (i : Fin 4) : Finset (ZMod 8) :=
  ![{0,1,5,6},{0,3,6,7},{1,2,4,5},{2,3,4,7}] i



















end Couret.InterIA.Cubic



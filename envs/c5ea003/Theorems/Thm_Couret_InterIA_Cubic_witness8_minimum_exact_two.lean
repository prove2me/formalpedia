-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_witness8_minimum_exact_two
-- name    : Couret.InterIA.Cubic.witness8_minimum_exact_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:16.639699+00:00
-- url     : https://prove2.me/theorems/1c73dc23-e846-4b1d-9526-400201d104a7
-- title:
--   A two-position cubic bank for the eight-cycle witness
-- statement:
--   For the fixed support $W_8(0)=\{0,1,5,6\}\subseteq\mathbb Z/8$, there is a set $Q$ of exactly two positions whose real cubic readings distinguish its cyclic four-point square fibre: $$|Q|=2.$$
--
--   This existence statement alone does not establish impossibility of one probe.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicWitness8.lean, lines 54–58; source file SHA-256 0cc66040496efdae6a0da5aaa1913b71bfc216fdce6455ba2090aafac04342a7; theorem Couret.InterIA.Cubic.witness8_minimum_exact_two

import Definitions.Def_Couret_CubicWitness8_775020fe3011
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
import Theorems.Thm_Couret_InterIA_Cubic_cyclic_four_two_cubic_probes
import Definitions.Def_Couret_CubicReconstruction_bc5d14805c7e

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem witness8_minimum_exact_two : ∃ Q : Finset (ZMod 8), Q.card=2 ∧
    Separates realCube (cyclicFourFibre 8 (witness8 0)) Q := by sorry


end Couret.InterIA.Cubic

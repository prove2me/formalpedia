-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_cyclic_four_two_cubic_probes
-- name    : Couret.InterIA.Cubic.cyclic_four_two_cubic_probes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:42.691569+00:00
-- url     : https://prove2.me/theorems/0815172e-6315-4f97-b478-b6fb5a00304f
-- title:
--   Two cubic probes separate a cyclic four-point fibre
-- statement:
--   Let $n>0$ and $S\subseteq\mathbb Z/n$ have four elements. There is a finite set of probe positions $Q\subseteq\mathbb Z/n$ with $$|Q|\le2$$ such that the real cubic-convolution readings at positions in $Q$ distinguish all members of the cyclic four-point square fibre of $S$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicReconstruction.lean, lines 84–106; source file SHA-256 c905b6a3c806a78c1db7ac9770bb76ec0a760869eeb7c80eacd35ac1d736463b; theorem Couret.InterIA.Cubic.cyclic_four_two_cubic_probes

import Definitions.Def_Couret_CubicReconstruction_bc5d14805c7e
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
import Theorems.Thm_Couret_InterIA_Cubic_small_family_probes
import Theorems.Thm_Couret_InterIA_Cubic_square_cube_support_injective
import Theorems.Thm_Couret_InterIA_Cubic_two_simple_cubic_probes
import Theorems.Thm_Couret_InterIA_Fibres_antipodal_free_four_ne_half_translate
import Definitions.Def_Couret_CubicSupport_513df21f9351
import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem cyclic_four_two_cubic_probes (n : ℕ) (hn : 0<n)
    (S : Finset (ZMod n)) (hS : S.card=4) :
    ∃ Q : Finset (ZMod n), Q.card≤2 ∧ Separates realCube (cyclicFourFibre n S) Q := by sorry


end Couret.InterIA.Cubic

-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_two_simple_cubic_probes
-- name    : Couret.InterIA.Cubic.two_simple_cubic_probes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:21.914496+00:00
-- url     : https://prove2.me/theorems/bf64acc0-63bb-4c48-945c-b467eb5e4fd2
-- title:
--   Two cubic coordinates reconstruct a two-simple four-support fibre
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $m>0$, let $C\subseteq\mathbb Z/(2m)\mathbb Z$ have two elements and contain no pair differing by $m$, and let $a$ be such that $C$ is disjoint from $\{a,a+m\}$. Set $S=C\cup\{a,a+m\}$ and $F=\{T:|T|=4, R_T=R_S\}$. There is a fixed set $Q$ of at most two residues such that
--
--   $$T,U\in F,\quad C_T|_Q=C_U|_Q\Longrightarrow T=U,$$
--
--   where $C_T$ is the real-valued ordered triple-sum count. This gives two nonadaptive cubic probes for the whole fibre.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicReconstruction.lean, lines 23–82; source file SHA-256 c905b6a3c806a78c1db7ac9770bb76ec0a760869eeb7c80eacd35ac1d736463b; theorem Couret.InterIA.Cubic.two_simple_cubic_probes

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
import Theorems.Thm_Couret_InterIA_Cubic_cube_eq_probe
import Theorems.Thm_Couret_InterIA_Cubic_parameterized_rectangle_probes
import Theorems.Thm_Couret_InterIA_Cubic_probe_union
import Theorems.Thm_Couret_InterIA_Cubic_small_family_probes
import Theorems.Thm_Couret_InterIA_Cubic_square_cube_support_injective
import Definitions.Def_Couret_CubicSupport_513df21f9351
import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem two_simple_cubic_probes (m : ℕ) (hm : 0<m)
    (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hfree : AntipodalFree m C) (ha : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    ∃ Q : Finset (ZMod (2*m)), Q.card≤2 ∧
      Separates realCube (originalFibre m (C ∪ fibre (m : ZMod (2*m)) a)) Q := by sorry




end Couret.InterIA.Cubic

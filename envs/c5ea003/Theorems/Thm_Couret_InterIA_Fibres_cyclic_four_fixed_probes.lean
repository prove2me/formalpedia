-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fixed_probes
-- name    : Couret.InterIA.Fibres.cyclic_four_fixed_probes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:37.98419+00:00
-- url     : https://prove2.me/theorems/c4d84ead-326e-4b8e-b731-b389b66e4e2b
-- title:
--   At most two fixed membership probes suffice
-- statement:
--   Let $n>0$ and $S\subseteq\mathbb Z/n$ have four elements. There exist $d\le2$ and a list of $d$ fixed positions whose membership answers separate the cyclic four-point square fibre, and $$|\mathcal F(S)|=2^d.$$
--
--   The case $d=0$ is permitted.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/FixedMembershipProbes.lean, lines 190–195; source file SHA-256 ad66985fbc01dce4c10be3faf60eae345c3ccda9af3d563dfd2ae2e57262cb82; theorem Couret.InterIA.Fibres.cyclic_four_fixed_probes

import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fibre_ncard
import Theorems.Thm_Couret_InterIA_Fibres_xor_family_fixed_probes
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem cyclic_four_fixed_probes (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=4) :
    ∃ d : ℕ, d ≤ 2 ∧ (cyclicFourFibre n S).ncard=2^d ∧
      ∃ q : Fin d → ZMod n, ProbeSeparates (cyclicFourFibre n S) q := by sorry


end Couret.InterIA.Fibres

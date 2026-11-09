-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_spanning_subbank_preserves_injectivity
-- name    : Couret.STROBO2TORS.recoh_spanning_subbank_preserves_injectivity
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:14.42239+00:00
-- url     : https://prove2.me/theorems/0cd8ebfe-6110-4bf9-be46-8d36198c176f
-- title:
--   A spanning subbank preserves linear-measurement injectivity
-- statement:
--   Let $V$ be a vector space over a field $K$, let $(\ell_i)_{i\in I}$ be linear functionals whose joint evaluation is injective, and let $s:J\to I$ select a subfamily. If the selected functionals span the same subspace of $V^*$ as the whole family, then
--
--   $$x\longmapsto(\ell_{s(j)}(x))_{j\in J}\text{ is injective}.$$
--
--   This permits reducing a measurement bank to a spanning subfamily without losing separation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohInformationSet.lean, lines 25–55; source file SHA-256 2c995fdd3163c7d085d3e54cdc03e3de75d6531a6e78bbfae2a5598e0da70298; theorem Couret.STROBO2TORS.recoh_spanning_subbank_preserves_injectivity

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false

/-!
RECOH: information-set extraction for a family of linear coordinate probes.

The general independent-subfamily theorem is standard linear algebra:
retain an independent subfamily spanning the original coordinate forms.
For a binary r-dimensional coordinate space, injectivity implies that
precisely r extracted coordinates suffice. These are not additional
conditions on the bank. Converting arbitrary additive binary characters
to linear forms is a separate interface.
-/

namespace Couret.STROBO2TORS

universe u

theorem recoh_spanning_subbank_preserves_injectivity
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    {ι κ : Type*}
    (bank : ι → Module.Dual K V) (selected : κ → ι)
    (hspan : Submodule.span K (Set.range (bank ∘ selected)) =
      Submodule.span K (Set.range bank))
    (hinj : Function.Injective (fun x : V => fun i : ι => bank i x)) :
    Function.Injective (fun x : V => fun j : κ => bank (selected j) x) := by sorry






end Couret.STROBO2TORS

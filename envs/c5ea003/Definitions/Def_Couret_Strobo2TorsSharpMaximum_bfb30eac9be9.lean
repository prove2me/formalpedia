-- Prove2me | Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
-- name    : Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:27.563866+00:00
-- url     : https://prove2.me/theorems/e40ba56a-8bb6-424c-b2e0-4283f976152c
-- title:
--   Maximum observed zero-free fibre size
-- statement:
--   For a finite abelian group, the defined maximum takes the largest cardinality among the observed nonempty zero-free parts of full three-support square fibres, with the natural-number finite-supremum convention giving zero when the family is empty. This is the scalar quantity whose sharp values are derived from torsion and doubling-image data.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The largest observed size of a nonempty zero-free ordered-square fibre.
The supremum of an empty Finset of fibres is zero. -/
noncomputable def maxObservedZeroFreeFibreSize : ℕ :=
  (zeroFreeFullFibres : Finset (Finset (Finset G))).sup Finset.card








































end Couret.STROBO2TORS



-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
-- name    : Couret.InterIA.SingletonNecessity.sevenDistinct_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:00:50.764922+00:00
-- url     : https://prove2.me/theorems/da6db0bd-d16d-4515-98c1-f1e3b4a7dd78
-- title:
--   Seven-label distinctness implies injectivity
-- statement:
--   Let $G$ be an abelian group and $x:\{0,\ldots,5\}\to G$. If the seven labels $0,x_0,\ldots,x_5$ are pairwise distinct, then $$x\text{ is injective}.$$
--
--   This forgets only the distinctness from zero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ExtractionBasics.lean, lines 56–62; source file SHA-256 65adcf683ecaaf85072801fa5eabac473cfd23154dfc02948e17c14bc16e67f1; theorem Couret.InterIA.SingletonNecessity.sevenDistinct_injective

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_SingletonNormalization_99875800f8c3
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sevenDistinct_injective (x : Fin 6 → G) (hd : SevenDistinct x) :
    Function.Injective x := by sorry




end Couret.InterIA.SingletonNecessity

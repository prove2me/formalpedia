-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_distinctLabels_of_injective_nonzero
-- name    : Couret.InterIA.SingletonNecessity.distinctLabels_of_injective_nonzero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:00:56.327237+00:00
-- url     : https://prove2.me/theorems/efdf4ad3-80c2-4449-8ab0-4d404fb24b88
-- title:
--   Six distinct nonzero entries give seven distinct labels
-- statement:
--   Let $G$ be an abelian group and $x:\{0,\ldots,5\}\to G$ be injective with $x_i\ne0$ for every index. Then $$0,x_0,\ldots,x_5\text{ are pairwise distinct}.$$
--
--   This verifies the seven-label distinctness predicate.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ExtractionBasics.lean, lines 32–45; source file SHA-256 65adcf683ecaaf85072801fa5eabac473cfd23154dfc02948e17c14bc16e67f1; theorem Couret.InterIA.SingletonNecessity.distinctLabels_of_injective_nonzero

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

theorem distinctLabels_of_injective_nonzero (x : Fin 6 → G)
    (hi : Function.Injective x) (hz : ∀ i, x i ≠ 0) : SevenDistinct x := by sorry








end Couret.InterIA.SingletonNecessity

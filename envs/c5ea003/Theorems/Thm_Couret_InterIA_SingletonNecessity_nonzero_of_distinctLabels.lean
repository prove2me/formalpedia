-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
-- name    : Couret.InterIA.SingletonNecessity.nonzero_of_distinctLabels
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:08.522608+00:00
-- url     : https://prove2.me/theorems/7b0e80c4-854c-4c78-b079-1e46943429b2
-- title:
--   Seven distinct labels force all six variables to be nonzero
-- statement:
--   Let $G$ be an abelian group, and let $x_0,\ldots,x_5\in G$ be such that $0,x_0,\ldots,x_5$ are pairwise distinct. Put $A=\{0,x_0,x_1,x_2\}$, $B=\{0,x_3,x_4,x_5\}$, $L=[x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2]$, and $R=[x_3,x_4,x_5,x_3+x_4,x_3+x_5,x_4+x_5]$. Then
--
--   $$x_i\ne0\qquad(0\le i<6).$$
--
--   This exposes the nonzero consequences of the distinct-label hypothesis.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ExtractionBasics.lean, lines 47–54; source file SHA-256 65adcf683ecaaf85072801fa5eabac473cfd23154dfc02948e17c14bc16e67f1; theorem Couret.InterIA.SingletonNecessity.nonzero_of_distinctLabels

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

theorem nonzero_of_distinctLabels (x : Fin 6 → G) (hd : SevenDistinct x) :
    ∀ i, x i ≠ 0 := by sorry






end Couret.InterIA.SingletonNecessity

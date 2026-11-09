-- Prove2me | Definitions.Def_Couret_ExtractionBasics_37ec1603f738
-- name    : Couret_ExtractionBasics_37ec1603f738
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:43.436346+00:00
-- url     : https://prove2.me/theorems/5d598d01-819f-4ffe-9b3b-4067c52293a2
-- title:
--   Rooted supports and diagonal matching patterns
-- statement:
--   Uses six group labels together with zero, required pairwise distinct. Defines left and right rooted four-point supports, their six off-diagonal sum lists, and two canonical patterns of equality among doubled labels: three cross equalities, or one equality within each side and one across sides. These definitions support extraction of matching constraints from square collisions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ExtractionBasics.lean; source file SHA-256 65adcf683ecaaf85072801fa5eabac473cfd23154dfc02948e17c14bc16e67f1

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
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_SingletonNormalization_99875800f8c3
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

abbrev SevenDistinct (x : Fin 6 → G) : Prop :=
  Function.Injective (fun i : Fin 7 => evaluation x (label i.val))

def supportLeft (x : Fin 6 → G) : Finset G := {0,x 0,x 1,x 2}
def supportRight (x : Fin 6 → G) : Finset G := {0,x 3,x 4,x 5}
def sumTermsLeft (x : Fin 6 → G) : List G :=
  [x 0,x 1,x 2,x 0+x 1,x 0+x 2,x 1+x 2]
def sumTermsRight (x : Fin 6 → G) : List G :=
  [x 3,x 4,x 5,x 3+x 4,x 3+x 5,x 4+x 5]
def CrossDoubles (x : Fin 6 → G) : Prop :=
  x 0+x 0=x 3+x 3 ∧ x 1+x 1=x 4+x 4 ∧ x 2+x 2=x 5+x 5
def MixedDoubles (x : Fin 6 → G) : Prop :=
  x 0+x 0=x 1+x 1 ∧ x 3+x 3=x 4+x 4 ∧ x 2+x 2=x 5+x 5











end Couret.InterIA.SingletonNecessity



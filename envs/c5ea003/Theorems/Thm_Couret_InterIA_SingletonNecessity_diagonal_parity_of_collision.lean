-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_diagonal_parity_of_collision
-- name    : Couret.InterIA.SingletonNecessity.diagonal_parity_of_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:29.938206+00:00
-- url     : https://prove2.me/theorems/95037704-4617-4de8-b529-e1de857ea4bc
-- title:
--   Equal square profiles have equal diagonal parities
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. For finite subsets $A,B$ of an abelian group with $R_A=R_B$, and any $z$ in the group,
--
--   $$|\{a\in A:2a=z\}|\equiv|\{b\in B:2b=z\}|\pmod2.$$
--
--   The off-diagonal ordered contributions disappear modulo two.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ExtractionBasics.lean, lines 64–67; source file SHA-256 65adcf683ecaaf85072801fa5eabac473cfd23154dfc02948e17c14bc16e67f1; theorem Couret.InterIA.SingletonNecessity.diagonal_parity_of_collision

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
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_SingletonNormalization_99875800f8c3
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem diagonal_parity_of_collision (A B : Finset G)
    (hc : ∀ z, orderedSquare A z=orderedSquare B z) (z : G) :
    diagonalCount A z % 2 = diagonalCount B z % 2 := by sorry


end Couret.InterIA.SingletonNecessity

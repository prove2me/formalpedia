-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_four_torsion_trivial_of_odd_annihilator
-- name    : Couret.InterIA.SingletonNecessity.four_torsion_trivial_of_odd_annihilator
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:51:18.860018+00:00
-- url     : https://prove2.me/theorems/0a7c7e8e-aa3e-4052-8d9f-7fd1ec25bf8f
-- title:
--   An odd annihilator excludes four-torsion
-- statement:
--   Let $H$ be an abelian group and $k\ge0$ such that $(2k+1)y=0$ for every $y\in H$. Then $$4y=0\Longrightarrow y=0.$$ In particular the assertion includes $k=0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/PrimaryReduction.lean, lines 10–29; source file SHA-256 ab87827fa5f33af12f833abbff68b1c49c6fbcf94b8b26736a01d6fd13dd2745; theorem Couret.InterIA.SingletonNecessity.four_torsion_trivial_of_odd_annihilator

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
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
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary Couret.InterIA.Parity
variable {P H : Type*} [AddCommGroup P] [AddCommGroup H]

theorem four_torsion_trivial_of_odd_annihilator (k : ℕ)
    (hH : ∀ y : H, (2*k+1) • y=0) :
    ∀ y : H, (4:ℕ) • y=0 → y=0 := by sorry










end Couret.InterIA.SingletonNecessity

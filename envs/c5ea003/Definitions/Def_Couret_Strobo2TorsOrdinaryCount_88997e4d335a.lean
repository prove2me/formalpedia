-- Prove2me | Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
-- name    : Couret_Strobo2TorsOrdinaryCount_88997e4d335a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:58.565163+00:00
-- url     : https://prove2.me/theorems/3cac5900-072a-490c-aad0-6dce01374e35
-- title:
--   Two-torsion profiles of ordinary and exceptional supports
-- statement:
--   For a finite abelian group with two-torsion subgroup $H$, profile $j$ filters ordinary or exceptional triple supports by $$|S\cap H|=j.$$ A parallel exceptional-parameter profile filters parameter triples by the profile of their realized support. These finite families organize the subsequent support, fibre and survival counts.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryCount.lean; source file SHA-256 36abdb7751662075f2a7470be2d1ccb52e577e35046510b06cdd5f29e66531f2

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

/-- Ordinary triples with exactly j vertices in H=G[2]. Unlike the
ordinary-fibre stratum, these are individual supports, not H-orbits. -/
def ordinarySupportsProfile (j : ℕ) : Finset (Finset G) :=
  (tripleSupportsProfile (G := G) j).filter
    (fun S => (squareFibre S).card = (twoTorsion : Finset G).card)

/-- Exceptional triples with exactly j vertices in H=G[2]. -/
def exceptionalSupportsProfile (j : ℕ) : Finset (Finset G) :=
  (tripleSupportsProfile (G := G) j).filter
    (fun S => (squareFibre S).card = 2 * (twoTorsion : Finset G).card)





















/-! ## Exceptional-support strata through their unique parameters -/

/-- Exceptional parameter triples with exactly j support points in G[2]. -/
def exceptionalParamsProfile (j : ℕ) : Finset ((G × G) × G) :=
  (exceptionalParams : Finset ((G × G) × G)).filter
    (fun p => (paramSupport p ∩ (twoTorsion : Finset G)).card = j)





/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS



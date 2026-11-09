-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Orbits_normal_form_geometric_data
-- name    : Couret.InterIA.Catalogue.Orbits.normal_form_geometric_data
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:57.290476+00:00
-- url     : https://prove2.me/theorems/68bd657c-3d99-4d6a-b698-242f97efd6db
-- title:
--   Geometric data of a normal form
-- statement:
--   For every positive natural $m$ and finite subsets $S,T\subseteq R=\mathbb Z/(2m)\mathbb Z$, assume $|S\cap T|=2$, there exist $a_0,b_0\in R$ with $S\setminus T=\{a_0,a_0+m\}$ and $T\setminus S=\{b_0,b_0+m\}$, and the ordered-pair sum counts of $S,T$ agree everywhere. There exist $a,b\in R$ with $S\setminus T=\{a,a+m\}$, $T\setminus S=\{b,b+m\}$, each of these two pairs disjoint from $C=S\cap T$, and $\delta=\pi(b-a)\ne0$, such that $F=X^\delta F$ and the additive order of $\delta$ is $2$ or $4$. Here $\pi$ is reduction modulo $m$, $X^y$ denotes the integer group-ring basis element at $y$, and $F=\sum_{c\in C}X^{\pi(c)}+X^{\pi(a)}+X^{\pi(b)}$ in $\mathbb Z[\mathbb Z/m\mathbb Z]$, with $X^xX^y=X^{x+y}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitAssembly.lean, lines 19–63; source file SHA-256 d6824040ee0d4b903b0ade8b6cd64bca166fac4d10f9c9e004600456bf0ae193; theorem Couret.InterIA.Catalogue.Orbits.normal_form_geometric_data

import Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Periods_residual_periods
import Theorems.Thm_Couret_InterIA_Catalogue_residual_equation
import Theorems.Thm_Couret_InterIA_Catalogue_residual_invariant
import Definitions.Def_Couret_OrbitGeometry_a2664a5897aa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Parity

theorem normal_form_geometric_data (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m)))
    (hn : Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∃ a b, S \ T=fibre (m : ZMod (2*m)) a ∧
      T \ S=fibre (m : ZMod (2*m)) b ∧
      Disjoint (S ∩ T) (fibre (m : ZMod (2*m)) a) ∧
      Disjoint (S ∩ T) (fibre (m : ZMod (2*m)) b) ∧
      projection m (b-a) ≠ 0 ∧
      residual m (S ∩ T) a b=A (projection m (b-a))*residual m (S ∩ T) a b ∧
      (addOrderOf (projection m (b-a))=2 ∨ addOrderOf (projection m (b-a))=4) := by sorry








end Couret.InterIA.Catalogue.Orbits

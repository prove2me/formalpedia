-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Orbits_collision_orbit_shapes
-- name    : Couret.InterIA.Catalogue.Orbits.collision_orbit_shapes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:18.800467+00:00
-- url     : https://prove2.me/theorems/e60b89c4-94a1-4b07-a868-5d0d0566c520
-- title:
--   collision orbit shapes
-- statement:
--   For every positive integer $m$ and finite subsets $S,T$ of $R=ℤ/(2m)ℤ$, assume $|S|=|T|=4$, that for every $z∈R$ the numbers of ordered pairs in $S²$ and $T²$ summing to $z$ agree, and that there are no unit $u∈R$ and $v∈R$ with $uS+v=T$. There exists $t∈\{0,m\}$ such that, with $T_t=T+t$ and $π:R→ℤ/mℤ$ reduction, there exist $a,b,c,d∈R$ with $S∖T_t=\{a,a+m\}$, $T_t∖S=\{b,b+m\}$, $c≠d$, and $S∩T_t=\{c,d\}$. Each of $π(c),π(d)$ differs from each of $π(a),π(b)$. Writing $δ=π(b-a)$, either $δ$ has additive order $2$ and $π(d)=π(c)+δ$, or $δ$ has additive order $4$ and $(π(c),π(d))$ equals $(π(a)+2δ,π(a)+3δ)$ in either order.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitAssembly.lean, lines 110–123; source file SHA-256 d6824040ee0d4b903b0ade8b6cd64bca166fac4d10f9c9e004600456bf0ae193; theorem Couret.InterIA.Catalogue.Orbits.collision_orbit_shapes

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
import Theorems.Thm_Couret_InterIA_Catalogue_Orbits_normal_form_orbit_shapes
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Definitions.Def_Couret_OrbitGeometry_a2664a5897aa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Parity

theorem collision_orbit_shapes (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧ OrbitShape m S (T.image (fun x => x+t)) := by sorry


end Couret.InterIA.Catalogue.Orbits

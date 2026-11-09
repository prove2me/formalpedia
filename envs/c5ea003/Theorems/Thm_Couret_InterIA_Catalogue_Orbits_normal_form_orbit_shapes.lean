-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Orbits_normal_form_orbit_shapes
-- name    : Couret.InterIA.Catalogue.Orbits.normal_form_orbit_shapes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:40.625049+00:00
-- url     : https://prove2.me/theorems/96afd0a6-44cc-408c-b71f-b1ce831fc6d3
-- title:
--   normal form orbit shapes
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. For every positive natural m and finite S,T⊆ℤ/(2m)ℤ, assume |S∩T|=2, there exist a₀,b₀ with S∖T={a₀,a₀+m} and T∖S={b₀,b₀+m}, and Q(S,z)=Q(T,z) for every z. Let π be reduction modulo m. Then there exist a,b,c,d∈ℤ/(2m)ℤ with S∖T={a,a+m}, T∖S={b,b+m}, c≠d, S∩T={c,d}, and each of π(c),π(d) unequal to each of π(a),π(b). Writing δ=π(b−a), either δ has additive order 2 and π(d)=π(c)+δ, or δ has additive order 4 and (π(c),π(d)) equals (π(a)+2δ,π(a)+3δ) or (π(a)+3δ,π(a)+2δ).
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitAssembly.lean, lines 81–108; source file SHA-256 d6824040ee0d4b903b0ade8b6cd64bca166fac4d10f9c9e004600456bf0ae193; theorem Couret.InterIA.Catalogue.Orbits.normal_form_orbit_shapes

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
import Theorems.Thm_Couret_InterIA_Catalogue_Orbits_normal_form_geometric_data
import Theorems.Thm_Couret_InterIA_Catalogue_residual_four_atoms
import Definitions.Def_Couret_OrbitGeometry_a2664a5897aa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Parity

theorem normal_form_orbit_shapes (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m)))
    (hn : Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) : OrbitShape m S T := by sorry




end Couret.InterIA.Catalogue.Orbits

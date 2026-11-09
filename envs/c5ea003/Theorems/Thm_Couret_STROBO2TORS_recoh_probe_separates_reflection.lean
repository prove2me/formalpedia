-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_probe_separates_reflection
-- name    : Couret.STROBO2TORS.recoh_probe_separates_reflection
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:18.823552+00:00
-- url     : https://prove2.me/theorems/b0eb5eef-71ed-4c5f-b4f1-6d07d0e9ce12
-- title:
--   A character distinguishes reflected triples when it detects the sign
-- statement:
--   Let $G$ be an abelian group. Let $R$ be a commutative integral domain with $2\ne0$, and let $\chi:G\to R$ satisfy $\chi(x+y)=\chi(x)\chi(y)$. For $v,d\in G$ with $\chi(d)=1$ and $\chi(v)\ne\chi(-v)$,
--
--   $$\chi(0)+\chi(v)+\chi(v+d)\ne\chi(0)+\chi(-v)+\chi(-v+d).$$
--
--   This is a scalar reflection-separation criterion, without torsion assumptions on $v,d$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohRankBounds.lean, lines 86–108; source file SHA-256 add8a12a52f7726a5c2b90e8bf4620a04e4cd4af53fa055a48c44e96579cec49; theorem Couret.STROBO2TORS.recoh_probe_separates_reflection

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-!
RECOH — bounded rank prerequisites for the universal character-bank claim.
All statements in this module are unconditional Lean theorems, but
they DO NOT yet constitute B(G) = r+s for arbitrary finite abelian G.

We distinguish elementary pigeonhole bounds (arbitrary functions) from the
stronger common two- and three-torsion character-mask construction still outstanding.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_probe_separates_reflection
    {R : Type*} [CommRing R] [IsDomain R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (v d : G) (hd : chi d = 1)
    (hv : chi v ≠ chi (-v))
    (htwo : (2 : R) ≠ 0) :
    recohTripleProbe chi 0 v (v + d) ≠
      recohTripleProbe chi 0 (-v) (-v + d) := by sorry


end Couret.STROBO2TORS

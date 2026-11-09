-- Prove2me | Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
-- name    : Couret.InterIA.NormalForm.even_cyclic_L4
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:55.255195+00:00
-- url     : https://prove2.me/theorems/68dc932e-ba27-465e-b1c9-e571a6c9499b
-- title:
--   even cyclic L4
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For every positive natural m and finite S,T⊆ℤ/(2m)ℤ with |S|=|T|=4, Q(S,z)=Q(T,z) for every z, and S,T not affinely equivalent, there exists t∈ℤ/(2m)ℤ with t=0 or t=m such that |S∩(T+t)|=2 and there exist a,b∈ℤ/(2m)ℤ with S∖(T+t)={a,a+m} and (T+t)∖S={b,b+m}, where T+t={x+t:x∈T}.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/L4Assembly.lean, lines 16–28; source file SHA-256 963e8dd3e3584e7170596d25b739b90c527798bb137acf05581e70913cf1549c; theorem Couret.InterIA.NormalForm.even_cyclic_L4

import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_normal_or_translation
import Theorems.Thm_Couret_InterIA_NormalForm_translation_is_affine
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem even_cyclic_L4 (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      Normal (m : ZMod (2*m)) S (T.image (fun x => x+t)) := by sorry






end Couret.InterIA.NormalForm

-- Prove2me | Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4_explicit
-- name    : Couret.InterIA.NormalForm.cyclic_four_L4_explicit
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:50:14.882866+00:00
-- url     : https://prove2.me/theorems/1387f574-b537-492a-bde9-4c582fdefb4b
-- title:
--   cyclic four L4 explicit
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For every natural n≥4 and finite S,T⊆ℤ/nℤ with |S|=|T|=4, Q(S,z)=Q(T,z) for every z, and S,T not affinely equivalent, n is even and there exists t∈ℤ/nℤ equal to 0 or to the residue of the natural quotient n/2 such that |S∩(T+t)|=2 and there exist a,b∈ℤ/nℤ with S∖(T+t)={a,a+n/2} and (T+t)∖S={b,b+n/2}. Here T+t={x+t:x∈T}, and n/2 is natural-number division before coercion into the ring.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/L4Assembly.lean, lines 51–61; source file SHA-256 963e8dd3e3584e7170596d25b739b90c527798bb137acf05581e70913cf1549c; theorem Couret.InterIA.NormalForm.cyclic_four_L4_explicit

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
import Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem cyclic_four_L4_explicit (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) :
    Even n ∧ ∃ t : ZMod n, (t=0 ∨ t=(n/2 : ℕ)) ∧
      (S ∩ T.image (fun x => x+t)).card=2 ∧
      ∃ a b : ZMod n,
        S \ T.image (fun x => x+t)={a,a+((n/2 : ℕ) : ZMod n)} ∧
        T.image (fun x => x+t) \ S={b,b+((n/2 : ℕ) : ZMod n)} := by sorry


end Couret.InterIA.NormalForm

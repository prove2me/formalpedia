-- Prove2me | solution 1 for UnitalMagmaDefect.NegMagma.of_mem_defectSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:03:35.886039+00:00
-- url     : https://prove2.me/submissions/3ecf0f06-bc00-494e-8368-03cd90c47ab8

import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect

open UnitalMagmaDefect Finset

universe u

open UnitalMagmaDefect UnitalMagmaDefect.NegMagma Finset in
/-- **Non-associative triples of the negation magma** are exactly those with `a ≠ c`. -/
theorem solution {M : Type u} [Mul M] [Fintype M] [DecidableEq M]
    (hcomm : ∀ a b : M, a * b = b * a)
    {M' : Type u} [Mul M'] [One M'] [Fintype M'] [DecidableEq M']
    (hl : ∀ a : M', 1 * a = a) (hr : ∀ a : M', a * 1 = a)
    {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (h2 : ∀ x y : G, x + x = y + y → x = y) (a b c : G) :
    ((of a : NegMagma G), of b, of c) ∈ defectSet (NegMagma G) ↔ a ≠ c := by
  have hmul : ∀ x y : G, (of x : NegMagma G) * of y = of (-(x + y)) := fun x y => rfl
  have hinj : ∀ x y : G, (of x : NegMagma G) = of y ↔ x = y :=
    fun x y => ⟨fun h => Option.some.inj h, fun h => h ▸ rfl⟩
  simp only [defectSet, Finset.mem_filter, Finset.mem_univ, true_and]
  show (of a * of b) * of c ≠ of a * (of b * of c) ↔ a ≠ c
  rw [hmul, hmul, hmul, hmul, ne_eq, hinj]
  constructor
  · intro h hac
    apply h
    subst hac
    abel
  · intro hac h
    apply hac
    apply h2
    have key : a + a - (c + c) = -(-(a + b) + c) - -(a + -(b + c)) := by abel
    rw [h, sub_self] at key
    exact sub_eq_zero.mp key

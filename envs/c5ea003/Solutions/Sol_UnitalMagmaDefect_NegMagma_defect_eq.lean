-- Prove2me | solution 1 for UnitalMagmaDefect.NegMagma.defect_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:09:36.301913+00:00
-- url     : https://prove2.me/submissions/905b8c8e-2d69-475a-a123-f4d1809acd93

import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect

open UnitalMagmaDefect Finset

universe u

open UnitalMagmaDefect UnitalMagmaDefect.NegMagma Finset in
/-- **The negation magma has associativity defect `|G|³ - |G|²`.** -/
theorem solution {M : Type u} [Mul M] [Fintype M] [DecidableEq M]
    (hcomm : ∀ a b : M, a * b = b * a)
    {M' : Type u} [Mul M'] [One M'] [Fintype M'] [DecidableEq M']
    (hl : ∀ a : M', 1 * a = a) (hr : ∀ a : M', a * 1 = a)
    {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (h2 : ∀ x y : G, x + x = y + y → x = y) :
    defect (NegMagma G) = (Fintype.card G) ^ 3 - (Fintype.card G) ^ 2 := by
  classical
  -- membership of a triple of group elements (the accepted `of_mem_defectSet_iff`)
  have hmem3 : ∀ a b c : G,
      ((of a : NegMagma G), of b, of c) ∈ defectSet (NegMagma G) ↔ a ≠ c := by
    intro a b c
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
  -- every non-associative triple consists of group elements with a ≠ c
  have hassoc : ∀ t : NegMagma G × NegMagma G × NegMagma G,
      t ∈ defectSet (NegMagma G) ↔ ∃ a b c : G, a ≠ c ∧ t = ((of a : NegMagma G), of b, of c) := by
    rintro ⟨x, y, z⟩
    rcases x with _ | a <;> rcases y with _ | b <;> rcases z with _ | c
    all_goals
      first
        | exact (hmem3 a b c).trans
            ⟨fun h => ⟨a, b, c, h, rfl⟩, fun ⟨a', b', c', h, he⟩ => by
              simp only [Prod.mk.injEq] at he
              have e1 : a = a' := Option.some.inj he.1
              have e3 : c = c' := Option.some.inj he.2.2
              rw [e1, e3]; exact h⟩
        | (constructor
           · intro h
             simp only [defectSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
             exact absurd rfl h
           · rintro ⟨a', b', c', _, he⟩
             simp only [Prod.mk.injEq] at he
             exact absurd he (by simp [NegMagma.of]))
  let emb : (G × G × G) ↪ (NegMagma G × NegMagma G × NegMagma G) :=
    ⟨fun t => ((of t.1 : NegMagma G), of t.2.1, of t.2.2), fun s t h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext_iff.mpr ⟨Option.some.inj h.1,
        Prod.ext_iff.mpr ⟨Option.some.inj h.2.1, Option.some.inj h.2.2⟩⟩⟩
  have hext : defectSet (NegMagma G)
      = (univ.filter (fun t : G × G × G => t.1 ≠ t.2.2)).map emb := by
    ext t
    rw [hassoc, Finset.mem_map]
    constructor
    · rintro ⟨a, b, c, hac, rfl⟩
      exact ⟨(a, b, c), by simp [hac], rfl⟩
    · rintro ⟨⟨a, b, c⟩, hs, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact ⟨a, b, c, hs, rfl⟩
  have hdiag : (univ.filter (fun t : G × G × G => t.1 = t.2.2)).card = Fintype.card G ^ 2 := by
    rw [sq, ← Fintype.card_prod, ← Finset.card_univ]
    refine Finset.card_nbij' (fun t => (t.1, t.2.1)) (fun p => (p.1, p.2, p.1)) ?_ ?_ ?_ ?_
    · intro t _; simp
    · intro p _; simp
    · intro t ht
      simp only [coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ht
      exact Prod.ext_iff.mpr ⟨rfl, Prod.ext_iff.mpr ⟨rfl, ht⟩⟩
    · intro p _; rfl
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (G × G × G)))
    (fun t : G × G × G => t.1 = t.2.2)
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, hdiag] at hsplit
  unfold defect
  rw [hext, Finset.card_map]
  have hne : (univ.filter (fun t : G × G × G => t.1 ≠ t.2.2)).card
      = (univ.filter (fun t : G × G × G => ¬ t.1 = t.2.2)).card := rfl
  rw [hne]
  have hcube : Fintype.card G * (Fintype.card G * Fintype.card G) = Fintype.card G ^ 3 := by ring
  rw [hcube] at hsplit
  omega

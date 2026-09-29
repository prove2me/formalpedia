-- Prove2me | Definitions.Def_Novelty_FriendshipChromaticPolynomial
-- name    : Novelty_FriendshipChromaticPolynomial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:26:34.00901+00:00
-- url     : https://prove2.me/theorems/b3ae01b4-4c18-4720-a4e0-6f837bfaaba9
-- title:
--   Aether Catalog definitions — Novelty_FriendshipChromaticPolynomial
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FriendshipChromaticPolynomial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FriendshipChromaticPolynomial.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Chromatic Polynomial of the Friendship (Windmill) Graph

This file computes, in closed form, the *chromatic counting function* of the **friendship graph**
`F_n` (also called the windmill graph, or Dutch windmill).  The friendship graph consists of a
single central person who is friends with everyone, together with `n` disjoint pairs of people, each
pair being mutual friends: geometrically, `n` triangles all sharing one common vertex.

In the "emotions" reading of graph coloring (assign each person one of `q` emotions so that no two
friends share the same emotion), `chromVal n q` counts the number of consistent emotion assignments
of `F_n` with a palette of `q` emotions.  This is the value `P(F_n, q)` of the chromatic polynomial.

## Main result

* `chromVal_friendship` :  `P(F_n, q) = q · ((q-1)(q-2))^n`.

  The central person picks any of `q` emotions; then, independently for each of the `n` triangles,
  the two outer people must both differ from the centre and from each other, giving `(q-1)(q-2)`
  admissible pairs per triangle.

## Consequences

* `friendship_chromVal_six`     :  with the six basic emotions, `P(F_n, 6) = 6 · 20^n` — this is the
                                   original "graph coloring with emotions" conjecture, now proved.
* `chromVal_pos_iff_colorable`  :  the counting function detects colorability.
* `friendship_colorable_three`  :  three emotions always suffice.
* `friendship_colorable_six`    :  the six basic emotions always suffice.
* `friendship_not_colorable_two`:  for `n ≥ 1`, two emotions never suffice (each triangle is a
                                   clique of size three).
* `friendship_chromaticNumber`  :  for `n ≥ 1`, the chromatic number of `F_n` is exactly `3`; hence,
                                   restricted to the emotional regime `k ≥ 3`, its emotional
                                   chromatic number is `3` and lies in the six-emotion window `[3,6]`.

The proof of the closed form is a genuine bijective count: proper colorings of `F_n` are put in
explicit bijection with a choice of centre colour together with, per triangle, an ordered pair of
colours avoiding the centre and each other (`frEquiv`), whose count is `(q-1)(q-2)` (`pairColors_card`).

The file is self-contained: it imports only Mathlib and redevelops the small amount of
chromatic-counting API it needs.
-/


namespace Catalog.Novelty.FriendshipChromaticPolynomial

open SimpleGraph Finset

/-! ## The friendship graph -/

/-- Adjacency of the friendship graph `F_n` on vertex set `Option (Fin n × Bool)`.
The centre is `none`; the two outer vertices of triangle `i` are `some (i, false)` and
`some (i, true)`.  The centre is adjacent to every outer vertex, and the two outer vertices of a
common triangle are adjacent to each other; there are no other edges. -/
def frAdj (n : ℕ) (x y : Option (Fin n × Bool)) : Prop :=
  match x, y with
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some p, some q => p.1 = q.1 ∧ p.2 ≠ q.2

instance frAdjDec (n : ℕ) : DecidableRel (frAdj n) :=
  fun x y => by cases x <;> cases y <;> unfold frAdj <;> infer_instance

/-- The **friendship (windmill) graph** `F_n`: `n` triangles glued at a common central vertex. -/
def friendship (n : ℕ) : SimpleGraph (Option (Fin n × Bool)) where
  Adj := frAdj n
  symm := by intro x y h; cases x <;> cases y <;> simp_all [frAdj]; tauto
  loopless := ⟨by rintro x h; cases x <;> simp_all [frAdj]⟩

instance (n : ℕ) : DecidableRel (friendship n).Adj := frAdjDec n

/-- The chromatic counting function `P(F_n, q)`: the number of proper colorings `V → Fin q` of the
friendship graph, i.e. the number of consistent assignments of `q` emotions. -/
def chromVal (n q : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun c : Option (Fin n × Bool) → Fin q => ∀ x y, (friendship n).Adj x y → c x ≠ c y)).card

/-! ## Counting the colourings of one triangle -/



/-! ## The colouring bijection -/

/-- **The structural bijection.** A proper colouring of `F_n` is exactly a choice of centre colour
`z : Fin q` together with, for each triangle `i`, an ordered pair of outer colours both avoiding `z`
and each other.  The forward map reads off the centre and each triangle's outer colours; the inverse
paints the centre with `z` and triangle `i`'s outer vertices with the recorded pair. -/
def frEquiv (n q : ℕ) :
    {c : Option (Fin n × Bool) → Fin q // ∀ x y, (friendship n).Adj x y → c x ≠ c y}
      ≃ Σ z : Fin q, (Fin n → {p : Fin q × Fin q // p.1 ≠ z ∧ p.2 ≠ z ∧ p.1 ≠ p.2}) where
  toFun := fun c =>
    ⟨c.1 none, fun i =>
      ⟨(c.1 (some (i, false)), c.1 (some (i, true))),
        c.2 (some (i, false)) none trivial,
        c.2 (some (i, true)) none trivial,
        c.2 (some (i, false)) (some (i, true)) ⟨rfl, Bool.false_ne_true⟩⟩⟩
  invFun := fun s =>
    ⟨fun v => match v with
      | none => s.1
      | some (i, b) => bif b then (s.2 i).1.2 else (s.2 i).1.1,
      by
        rintro x y h
        cases x with
        | none => cases y with
          | none => exact absurd h (by simp [friendship])
          | some p =>
            obtain ⟨i, b⟩ := p; have := (s.2 i).2; cases b <;> simp_all <;> tauto
        | some p =>
          obtain ⟨i, a⟩ := p
          cases y with
          | none => have := (s.2 i).2; cases a <;> simp_all
          | some p2 =>
            obtain ⟨j, b⟩ := p2
            obtain ⟨hij, hab⟩ : i = j ∧ a ≠ b := h
            subst hij
            have := (s.2 i).2.2.2
            cases a <;> cases b <;> simp_all [eq_comm]⟩
  left_inv := by
    rintro ⟨c, hc⟩; ext v
    cases v with
    | none => rfl
    | some p => obtain ⟨i, b⟩ := p; cases b <;> rfl
  right_inv := by rintro ⟨z, f⟩; congr 1

/-! ## The chromatic polynomial of the friendship graph -/


/-! ## Consequences -/







end Catalog.Novelty.FriendshipChromaticPolynomial



-- Prove2me | solution 1 for BerggrenPrice.word_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:04:19.55927+00:00
-- url     : https://prove2.me/submissions/fe08377d-d3c1-46ab-be37-b9a7ab310762

-- Sol generated from Algebra/BerggrenPriceInterlock/Core.lean
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Core
import Theorems.Thm_BerggrenPrice_isNode_root

/-!
# Berggren–Price interlock, Part I: an abstract ternary descent framework

Both classical trees of primitive Pythagorean triples (Barning–Hall–Berggren and Price)
become, in the *Euclid parameter* coordinates `(m, n)`, ternary trees on the set

  `Node = {(m,n) : 1 ≤ n < m, gcd(m,n) = 1, m + n odd}`

rooted at `(2,1)`.  This file isolates the purely combinatorial content that makes such a
family of three maps a *tree*: every node is `applyWord w root` for a **unique** word `w`.

The five hypotheses are: the maps preserve nodes, strictly increase the size `m + n`,
are injective, have pairwise disjoint images on nodes, and every non-root node has a
parent.  Both concrete trees are shown to satisfy them in
`Algebra.BerggrenPriceInterlock.Trees`.

## Main results

* `IsNode.size_ge` — every node has size `≥ 3`, with equality only at the root.
* `exists_word` — existence of a root-to-node word (Fermat descent).
* `word_unique` — uniqueness of that word (disjointness of the three subtrees).
* `exists_unique_word` — the two combined: the tree is a bijection `words ≃ nodes`.
-/

open BerggrenPrice






theorem BerggrenPrice.IsNode.size_ge {v : Node} (h : IsNode v) : 3 ≤ size v := by
  obtain ⟨h1, h2, -, -⟩ := h
  simp only [size]
  omega




variable (f : Fin 3 → Node → Node)




variable (hmap : ∀ i v, IsNode v → IsNode (f i v))

include hmap in
/-- Every word applied to a node yields a node. -/
theorem isNode_applyWord (w : List (Fin 3)) {v : Node} (hv : IsNode v) :
    IsNode (applyWord f w v) := by
  induction w with
  | nil => exact hv
  | cons i w ih => exact hmap i _ ih

variable (hsize : ∀ i v, IsNode v → size v < size (f i v))
variable (hparent : ∀ v, IsNode v → v ≠ root → ∃ i u, IsNode u ∧ f i u = v)


variable (hinj : ∀ i u v, f i u = f i v → u = v)
variable (hdisj : ∀ i j u v, IsNode u → IsNode v → f i u = f j v → i = j)





open BerggrenPrice in
include hmap hsize hinj hdisj in
theorem solution: ∀ (w w' : List (Fin 3)),
    applyWord f w root = applyWord f w' root → w = w' := by
  have hroot : IsNode root := isNode_root
  have hne : ∀ (i : Fin 3) (u : Node), IsNode u → f i u ≠ root := by
    intro i u hu h
    have h1 := hsize i u hu
    rw [h] at h1
    have h2 : (3 : ℤ) ≤ size u := hu.size_ge
    have h3 : size root = (3 : ℤ) := rfl
    omega
  intro w
  induction w with
  | nil =>
    intro w' h
    cases w' with
    | nil => rfl
    | cons j w' =>
      exact absurd (h.symm) (hne j _ (isNode_applyWord f hmap w' hroot))
  | cons i w ih =>
    intro w' h
    cases w' with
    | nil => exact absurd h (hne i _ (isNode_applyWord f hmap w hroot))
    | cons j w' =>
      have hij : i = j :=
        hdisj i j _ _ (isNode_applyWord f hmap w hroot) (isNode_applyWord f hmap w' hroot) h
      subst hij
      have := hinj i _ _ h
      rw [ih w' this]

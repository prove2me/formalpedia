-- Prove2me | solution 1 for BerggrenPrice.exists_word
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:04:18.989254+00:00
-- url     : https://prove2.me/submissions/e20fef46-71c5-4395-aea4-56d0fa4bd70d

-- Sol generated from Algebra/BerggrenPriceInterlock/Core.lean
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Core

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


variable (hsize : ∀ i v, IsNode v → size v < size (f i v))
variable (hparent : ∀ v, IsNode v → v ≠ root → ∃ i u, IsNode u ∧ f i u = v)


variable (hinj : ∀ i u v, f i u = f i v → u = v)
variable (hdisj : ∀ i j u v, IsNode u → IsNode v → f i u = f j v → i = j)





open BerggrenPrice in
include hsize hparent in
theorem solution: ∀ (v : Node), IsNode v → ∃ w : List (Fin 3), applyWord f w root = v := by
  intro v
  induction hn : (size v).toNat using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    intro hv
    by_cases hr : v = root
    · exact ⟨[], by simp [hr, applyWord]⟩
    · obtain ⟨i, u, hu, hfu⟩ := hparent v hv hr
      have hlt : size u < size v := by
        have := hsize i u hu
        rw [hfu] at this; exact this
      have h3u : 3 ≤ size u := hu.size_ge
      have hkey : (size u).toNat < k := by
        subst hn; omega
      obtain ⟨w, hw⟩ := ih (size u).toNat hkey u rfl hu
      exact ⟨i :: w, by simp [hw, hfu, applyWord]⟩

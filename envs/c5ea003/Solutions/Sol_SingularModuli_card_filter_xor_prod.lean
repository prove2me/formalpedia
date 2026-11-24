-- Prove2me | solution 1 for SingularModuli.card_filter_xor_prod
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:56:19.518213+00:00
-- url     : https://prove2.me/submissions/1848222f-ce7a-4ceb-9ae4-f40d06c8a6f8

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount

open SingularModuli

open Polynomial Finset FactoringBarriers

namespace SingularModuli

theorem solution {p q : ℕ} [NeZero p] [NeZero q]
    (A : Finset (ZMod p)) (B : Finset (ZMod q)) :
    (Finset.univ.filter (fun z : ZMod p × ZMod q => Xor (z.1 ∈ A) (z.2 ∈ B))).card
      = A.card * (q - B.card) + (p - A.card) * B.card := by
  classical
  have hset : (Finset.univ.filter (fun z : ZMod p × ZMod q => Xor (z.1 ∈ A) (z.2 ∈ B)))
      = A ×ˢ (Finset.univ \ B) ∪ (Finset.univ \ A) ×ˢ B := by
    ext z
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_product, Finset.mem_product,
      Finset.mem_sdiff, Finset.mem_sdiff]
    simp only [Finset.mem_univ, true_and, Xor]
    tauto
  have hdisj : Disjoint (A ×ˢ (Finset.univ \ B)) ((Finset.univ \ A) ×ˢ B) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [Finset.mem_product] at hz1 hz2
    exact (Finset.mem_sdiff.mp hz2.1).2 hz1.1
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ,
    Finset.card_univ, Finset.card_univ, ZMod.card p, ZMod.card q]

end SingularModuli

open SingularModuli

theorem solution {p q : ℕ} [NeZero p] [NeZero q]
    (A : Finset (ZMod p)) (B : Finset (ZMod q)) :
    (Finset.univ.filter (fun z : ZMod p × ZMod q => Xor (z.1 ∈ A) (z.2 ∈ B))).card
      = A.card * (q - B.card) + (p - A.card) * B.card :=
  SingularModuli.solution A B

#print axioms solution

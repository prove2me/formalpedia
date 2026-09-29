-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_edge_retention_card
-- name    : mme_stothers_phi134_cyclic_edge_retention_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:15:33.733075+00:00
-- url     : https://prove2.me/theorems/ce808060-c86d-46aa-b2cf-81867d29a52c
-- title:
--   $\Phi_{1,3,4}$ exact per-edge hash retention count
-- statement:
--   Fix an exact cyclic $\Phi_{1,3,4}$ edge and let $S\subseteq\mathbb Z/p\mathbb Z$ be any allowed-label set, with prime $p\ge7$. Choose the $6N+1$ affine weight coordinates and one offset coordinate uniformly. The number of hash states for which all three cyclic vertex labels of the edge agree at a value in $S$ is exactly
--
--   $$
--   |S|\,p^{6N}.
--   $$
--
--   The cyclic arithmetic-progression identity reduces equality of all three labels to one free allowed label and one affine equation determining the offset coordinate. The remaining $6N$ weight coordinates are free. This exact per-edge retention count supplies the first-moment term in the type-2 isolation argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, affine hashing and progression-free selection in Lemma 3.3 (pp. 359–361), specialized to $\Phi_{1,3,4}$ in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_edge_retention_card
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e : CyclicExactEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
        S.card * p ^ (6 * N) := by
  sorry

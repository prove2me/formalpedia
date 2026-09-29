-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_pair_retention_card_le
-- name    : mme_stothers_phi134_cyclic_pair_retention_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:26:31.499326+00:00
-- url     : https://prove2.me/theorems/242d8095-736c-412f-b9fb-ca76156a29df
-- title:
--   $\Phi_{1,3,4}$ joint retention bound for colliding edge pairs
-- statement:
--   Let $e\ne f$ be two exact cyclic $\Phi_{1,3,4}$ edges sharing one cyclic vertex, and let $p\ge7$ be prime. For any allowed-label set $S$, the number of affine hash states that retain both edges is at most
--
--   $$
--   p^{6N}.
--   $$
--
--   Because the full three-vertex projection is injective, the distinct edges differ at some other vertex. The reusable cyclic mode code then supplies a weight coordinate with a nonzero coefficient in the difference of their hash labels. Joint retention imposes two independent affine equations: equality of the differing vertex labels determines one weight coordinate, while equality within one retained edge determines the offset coordinate. Thus at most the remaining $6N$ coordinates are free. This is the pairwise collision bound required for type-2 pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, collision counting in the type-2 affine-hashing argument of Lemma 3.3 (pp. 359–361), specialized to $\Phi_{1,3,4}$ in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_pair_retention_card_le
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e f : CyclicExactEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) (hne : e ≠ f) (shared : Fin 3)
    (hshared : cyclicModeWord e shared = cyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma delta) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : CyclicExactEdge N alpha beta gamma delta) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
    ((Finset.univ.filter (fun q ↦ retain q e ∧ retain q f)).card) ≤
      p ^ (6 * N) := by
  sorry

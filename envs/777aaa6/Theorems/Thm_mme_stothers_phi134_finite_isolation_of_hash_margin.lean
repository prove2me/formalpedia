-- Prove2me | Theorems.Thm_mme_stothers_phi134_finite_isolation_of_hash_margin
-- name    : mme_stothers_phi134_finite_isolation_of_hash_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:46:42.769723+00:00
-- url     : https://prove2.me/theorems/cc841109-900f-4449-b70c-5c5891ddfd8b
-- title:
--   Phi134 finite isolation from the sharp hash margin
-- statement:
--   Let p be a prime at least 7, let S be a three-term-progression-free subset of Z/pZ, and fix an exact Phi_(1,3,4) profile of length 2N. Write D_* for the product of its three sharp cyclic mode-fiber degrees and V for the product of the three marginal multinomial counts. If a real loss parameter L satisfies
--
--   $$
--   p^2L+3D_*^2\le D_*|S|,
--   $$
--
--   then some affine hash state retains a finite subfamily K of exact cyclic edges such that every cyclic vertex projection is injective on K, every coordinatewise-supported three-edge mixture in K is diagonal, and
--
--   $$
--   |K|\ge V L.
--   $$
--
--   This is the finite isolation interface connecting the exact Phi_(1,3,4) profile counts and affine collision estimates to an induced diagonal family. It is designed to be combined with the source-specific tensor-block realization and the asymptotic choice of p, S, and L.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, Type-2 pruning and affine hashing in Lemma 3.3 (pp. 359–361), specialized to the Phi_(1,3,4) constituent in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Mathlib.Data.Nat.Choose.Multinomial

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_finite_isolation_of_hash_margin
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : alpha + beta + gamma + delta = N)
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (loss : ℝ) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let State := (I → ZMod p) × ZMod p
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : State) (i : Fin 3)
        (e : CyclicExactEdge N alpha beta gamma delta) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    let retain := fun (q : State)
        (e : CyclicExactEdge N alpha beta gamma delta) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    let Dstar := D 0 * (D 1 * D 2)
    let V := ∏ i : Fin 3,
      Nat.multinomial Finset.univ
        (marginalMultiplicity N alpha beta gamma delta i)
    ((p ^ 2 : ℕ) : ℝ) * loss +
          3 * (Dstar : ℝ) * (Dstar : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ) →
      ∃ q : State,
        ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
          kept ⊆ (edgeFinset N alpha beta gamma delta).filter (retain q) ∧
          (∀ i : Fin 3,
            Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
          (∀ x y z : kept,
            CyclicCoordinatewiseSupported x.1 y.1 z.1 →
              x = y ∧ y = z) ∧
          (V : ℝ) * loss ≤ (kept.card : ℝ) := by
  sorry

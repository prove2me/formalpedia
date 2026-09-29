-- Prove2me | solution 1 for ECMParity.affine_card_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:43:33.53133+00:00
-- url     : https://prove2.me/submissions/7907b558-abd9-4e53-aad3-5c928e68e330

-- Sol generated from Algebra/ECMParityCore.lean
import Mathlib
import Definitions.Def_Algebra_ECMParityCore
import Theorems.Thm_ECMParity_card_sqrt_fiber_mod_two
/-
# ECM-PARITY, core: the parity of the point count of `y² = x³ + A x + B`

For an odd prime `p` and `A B : ZMod p` put

  `curveCard A B = 1 + #{(x,y) ∈ (ZMod p)² : y² = x³ + A x + B}`

(the `1` is the point at infinity of the projective Weierstrass model).

The main result of this file is the **parity dichotomy**

  `2 ∣ curveCard A B  ↔  the cubic x³ + A x + B has a root in ZMod p`

valid whenever the cubic is separable (`Δ = -4A³ - 27B² ≠ 0`).  Equivalently:
`#E` is odd exactly when Frobenius is a `3`-cycle on the roots of the cubic
(the cubic is irreducible over `𝔽_p`; see `ECMParityFrobenius.lean`).

The proof is elementary and self-contained:

* fibrewise counting: over each `x` the fibre `{y : y² = f x}` has odd
  cardinality iff `f x = 0`, hence `#affine ≡ #roots (mod 2)`;
* a separable cubic has `0`, `1` or `3` roots (never `2`), so `#roots` is odd
  iff `#roots ≠ 0`.

§0 collects the purely algebraic facts about a depressed cubic over an arbitrary
field (Vieta, the third root, the discriminant as a square of the root
difference product).  These are reused over the cubic extension `𝔽_{p³}` in
`ECMParityFrobenius.lean`.
-/

open ECMParity

open Finset

/-! ## 0. Depressed cubics over an arbitrary field -/




variable {F : Type*} [Field F] {A B a b x : F}









/-! ## 1. Fibrewise counting over `𝔽_p` -/

variable {p : ℕ} [Fact p.Prime]








/-! ## 2. A separable cubic has `0`, `1` or `3` roots -/




/-! ## 3. The parity dichotomy -/




open ECMParity in
theorem solution(hp : p ≠ 2) (A B : ZMod p) :
    (((affinePoints A B).card : ZMod 2)) = ((rootSet A B).card : ZMod 2) := by
  have h1 : (affinePoints A B).card
      = ∑ x : ZMod p, (univ.filter (fun y : ZMod p => y ^ 2 = cubic A B x)).card := by
    rw [affinePoints, card_filter]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [card_filter]
  have h2 : ((rootSet A B).card : ZMod 2)
      = ∑ x : ZMod p, (if cubic A B x = 0 then (1 : ZMod 2) else 0) := by
    rw [rootSet, card_filter]
    push_cast
    exact Finset.sum_congr rfl (fun x _ => by split <;> simp)
  rw [h1, h2]
  push_cast
  exact Finset.sum_congr rfl (fun x _ => card_sqrt_fiber_mod_two hp _)

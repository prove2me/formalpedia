-- Prove2me | solution 2 for Bridges.AlexanderTorus.alexander_dvd_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-19T22:23:00.096298+00:00
-- url     : https://prove2.me/submissions/20c8c61c-79c3-4bcf-8623-2c0c552a1635

-- Sol generated from Bridges/AlexanderKnotNumberBridgeIII.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_alexander_eq_prod_cyclotomic
import Theorems.Thm_Bridges_AlexanderTorus_odd_of_dvd_odd
/-
# The Knot–Number bridge, third cycle: divisibility, separability, duality

Three structural theorems about the Alexander polynomial `A_N` of the torus knot
`T(2,N)`, all consequences of the cyclotomic factorization proved in
`Bridges.AlexanderKnotNumberBridge`:

* `alexander_dvd_iff_dvd` : **the divisibility bridge**
  `A_d ∣ A_M ↔ d ∣ M` (odd `d, M > 1`).
  Divisibility of torus-knot Alexander polynomials is *exactly* divisibility of the
  knot parameters — the divisor lattice of `N` is faithfully encoded in the
  divisibility order of the polynomials.
* `alexander_separable_rat` / `alexander_squarefree_rat` : `A_N` is separable
  (hence squarefree) over `ℚ`: the `N-1` roots are pairwise distinct, so the
  Alexander module `ℚ[X]/(A_N)` is a product of `τ(N)-1` distinct cyclotomic fields.
* `alexander_reverse` : `A_N` is palindromic, `A_N.reverse = A_N`, the polynomial
  shadow of Poincaré duality for the knot complement.
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The divisibility bridge -/






/-! ## Separability: the `N-1` roots are distinct -/




/-! ## Palindromicity (Poincaré duality shadow) -/




open Bridges.AlexanderTorus in
theorem solution{d M : ℕ} (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
    (hdvd : d ∣ M) : alexander d ∣ alexander M := by
  have hd : Odd d := odd_of_dvd_odd hM hdvd
  rw [alexander_eq_prod_cyclotomic hd hd1, alexander_eq_prod_cyclotomic hM hM1]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro e he
  obtain ⟨he1, hemem⟩ := Finset.mem_erase.1 he
  exact Finset.mem_erase.2
    ⟨he1, Nat.mem_divisors.2 ⟨(Nat.mem_divisors.1 hemem).1.trans hdvd, by omega⟩⟩

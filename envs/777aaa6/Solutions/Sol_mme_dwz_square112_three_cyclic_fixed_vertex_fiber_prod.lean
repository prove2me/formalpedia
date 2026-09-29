-- Prove2me | solution 1 for mme_dwz_square112_three_cyclic_fixed_vertex_fiber_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T08:19:22.294887+00:00
-- url     : https://prove2.me/submissions/f677b0d6-77f9-4c29-923c-57ec909754be

import Theorems.Thm_mme_dwz_square112_exact_profile_marginals_and_fibers
open MME.DWZSquare112
open scoped BigOperators
set_option autoImplicit false

theorem solution (N : ℕ) (c : Fin 4 → ℕ) (v : Fin 3 → Fin N → Fin 3)
    (hv : ∀ i a : Fin 3, Fintype.card {j : Fin N // v i j = a} = marginal c i a) :
    Nat.card {t : Fin 3 → ExactWord N c // ∀ i, modeWord (t i) i = v i}
      = ∏ i : Fin 3, ∏ a : Fin 3,
          (marginal c i a).factorial /
            ∏ r : {r : Fin 4 // row r i = a}, (c r.1).factorial := by
  have hfib := (mme_dwz_square112_exact_profile_marginals_and_fibers N c).2
  rw [Nat.card_congr (@Equiv.subtypePiEquivPi (Fin 3) (fun _ => ExactWord N c)
        (fun i w => modeWord w i = v i)), Nat.card_pi]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact hfib i (v i) (hv i)

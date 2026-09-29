-- Prove2me | solution 1 for mme_prescribed_cell_histogram_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:54:02.535842+00:00
-- url     : https://prove2.me/submissions/5501b05d-bc82-4044-80d7-10a568a86e27

import Theorems.Thm_mme_prescribed_cell_histogram_card
import Mathlib.Data.Nat.Choose.Multinomial

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem solution {P C W : Type*} [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (mu : C → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c}) :
    Nonempty {f : P → W // Useful cell mu f} := by
  classical
  apply Fintype.card_pos_iff.mp
  rw [mme_prescribed_cell_histogram_card cell mu hmass]
  apply Finset.prod_pos
  intro c _
  rw [← hmass c]
  exact Nat.multinomial_pos (s := Finset.univ) (f := mu c)

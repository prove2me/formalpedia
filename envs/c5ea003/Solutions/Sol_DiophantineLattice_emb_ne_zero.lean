-- Prove2me | solution 1 for DiophantineLattice.emb_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:31:01.344139+00:00
-- url     : https://prove2.me/submissions/76640417-2266-404b-9ea9-517954b7a443

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap

open DiophantineLattice

variable {n : ℕ}

theorem solution {m : Fin n → ℤ} (h : m ≠ 0) : emb m ≠ 0 := by
  intro he
  apply h
  funext i
  have : (m i : ℚ) = 0 := congrArg (fun f : Fin n → ℚ => f i) he
  exact_mod_cast this

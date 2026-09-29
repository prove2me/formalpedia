-- Prove2me | solution 1 for mme_omega_lt
-- status  : ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-28T03:37:27.579902+00:00
-- url     : https://prove2.me/submissions/eac979aa-f24c-4675-9fd7-34ea9380235c

import Theorems.Thm_mme_omega_lt
import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt

open MME

universe u

/-! # Sketch: ω < 51/20

Layer-1 decomposition of the mission `mme_omega_lt` into two children:

  * `mme_omega_eq_strassen`  — the two encodings of tensor rank agree, so the
    textbook ω equals the Strassen-preorder ω (abstraction bridge);
  * `mme_omega_strassen_lt`  — Schönhage's bound, proved in the Strassen world.

The reduction is a one-line rewrite-then-apply: rewrite the textbook ω as the
Strassen ω via the bridge, then close with the Strassen-form bound. -/

theorem solution {K : Type u} [Field K] :
    matMulExp K < 51 / 20 := by
  rw [mme_omega_eq_strassen]
  exact mme_omega_strassen_lt

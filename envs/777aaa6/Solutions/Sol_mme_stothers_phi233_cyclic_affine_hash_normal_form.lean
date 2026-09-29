-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_affine_hash_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:30:52.838844+00:00
-- url     : https://prove2.me/submissions/e209602f-a3cb-4b8b-adfb-19a3eb8ef573

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

open BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicAmbientEdge N alpha beta gamma delta) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset i e =
      shift + (![0, 12 * offset, 6 * offset] : Fin 3 → ZMod p) i +
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          cyclicHashModeCode p N i (cyclicModeWord e i) r j * w r j := by
  have hsumMul (f : Fin (2 * N) → ZMod p) (a : ZMod p) :
      (∑ j, f j) * a = ∑ j, f j * a := by
    simpa using
      (Finset.sum_mul (Finset.univ : Finset (Fin (2 * N))) f a)
  have hscale2 (u : Fin (2 * N) → Fin 5)
      (v : Fin (2 * N) → ZMod p) :
      (∑ j, ((u j).val : ZMod p) * v j * 2) * 2 =
        ∑ j, ((u j).val : ZMod p) * v j * 4 := by
    calc
      _ = ∑ j,
          (((u j).val : ZMod p) * v j * 2) * 2 := hsumMul _ 2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have hscale4 (u : Fin (2 * N) → Fin 5)
      (v : Fin (2 * N) → ZMod p) :
      (∑ j, (-((u j).val : ZMod p) * v j + v j * 4)) * 4 =
        ∑ j, (-((u j).val : ZMod p) * v j * 4 + v j * 16) := by
    calc
      _ = ∑ j,
          (-((u j).val : ZMod p) * v j + v j * 4) * 4 := hsumMul _ 4
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  fin_cases i
  · simp [cyclicAffineHash, cyclicHashModeCode, cyclicModeWord,
      doubledXHash, doubledYHash, doubledZHash, Fin.sum_univ_succ]
    ring_nf
    rw [hscale2 (e.2.2.1 1) (w 2)]
    have hb := hscale4 (e.2.1.1 2) (w 1)
    simp only [neg_mul] at hb
    rw [hb]
  · simp [cyclicAffineHash, cyclicHashModeCode, cyclicModeWord,
      doubledXHash, doubledYHash, doubledZHash, Fin.sum_univ_succ]
    ring_nf
    rw [hscale2 (e.2.1.1 0) (w 1)]
    have hc := hscale4 (e.2.2.1 2) (w 2)
    simp only [neg_mul] at hc
    rw [hc]
  · simp [cyclicAffineHash, cyclicHashModeCode, cyclicModeWord,
      doubledXHash, doubledYHash, doubledZHash, Fin.sum_univ_succ]
    ring

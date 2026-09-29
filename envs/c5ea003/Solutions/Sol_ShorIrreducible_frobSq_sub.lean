-- Prove2me | solution 1 for ShorIrreducible.frobSq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:18:10.168771+00:00
-- url     : https://prove2.me/submissions/98cd6fc2-b211-4db5-81a3-7134fca800e9

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {α β : Type*} [Fintype α] [Fintype β] (M A : Matrix α β ℂ) :
    frobSq (M - A) = frobSq M + frobSq A - 2 * (frobInner M A).re := by
  -- the parallelogram identity for a single complex entry
  have hpt : ∀ z w : ℂ, ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (star z * w).re := by
    intro z w
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.star_def]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  -- the real part of the Frobenius inner product, re-indexed to match `frobSq`
  have hfi : (frobInner M A).re = ∑ f : α, ∑ g : β, (star (M f g) * A f g).re := by
    rw [frobInner, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Complex.re_sum]
    simp only [Complex.re_sum]
    rw [Finset.sum_comm]
  have key : ∀ f : α, ∀ g : β, ‖(M - A) f g‖ ^ 2
      = ‖M f g‖ ^ 2 + ‖A f g‖ ^ 2 - 2 * (star (M f g) * A f g).re := by
    intro f g
    rw [Matrix.sub_apply]
    exact hpt _ _
  rw [frobSq, frobSq, frobSq, hfi]
  rw [Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun g _ => key f g))]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

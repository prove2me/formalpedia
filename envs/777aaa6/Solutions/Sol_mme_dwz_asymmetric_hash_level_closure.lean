-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_level_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T08:19:22.849672+00:00
-- url     : https://prove2.me/submissions/6d37c0b1-4875-4fe4-aa29-f0e80ebf24e9

import Definitions.Def_mme_dwz_asymmetric_affine_hash
open MME BigOperators
set_option autoImplicit false

theorem solution {p N : ℕ} [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (levelSum : ZMod p) (ω : DWZAsymmetricHashState p N)
    (I J K : Fin (N + 1) → ZMod p)
    (hlevel : ∀ t, I t + J t + K t = levelSum)
    (s : ZMod p)
    (hX : dwzAsymmetricHashX ω I = s)
    (hY : dwzAsymmetricHashY ω J = s) :
    dwzAsymmetricHashZ levelSum ω K = s := by
  unfold dwzAsymmetricHashX at hX
  unfold dwzAsymmetricHashY at hY
  unfold dwzAsymmetricHashZ
  have key : ∀ t, levelSum - K t = I t + J t := by
    intro t; rw [← hlevel t]; ring
  have hI : ∑ t, I t * ω.weight t = s - ω.b0 := by rw [← hX]; ring
  have hJ : ∑ t, J t * ω.weight t = s - ω.b0 - ω.w0 := by rw [← hY]; ring
  have hsplit : ∑ t, (levelSum - K t) * ω.weight t
      = (∑ t, I t * ω.weight t) + (∑ t, J t * ω.weight t) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [key t]; ring
  rw [hsplit, hI, hJ]
  field_simp
  ring

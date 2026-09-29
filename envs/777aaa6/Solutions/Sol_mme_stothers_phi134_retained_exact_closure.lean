-- Prove2me | solution 1 for mme_stothers_phi134_retained_exact_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:34:18.605659+00:00
-- url     : https://prove2.me/submissions/2172f2d3-f543-4480-b64a-b68c21f3c0a8

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi134_cyclic_affine_hash_AP
import Theorems.Thm_mme_stothers_phi134_cyclic_supported_mix_closure

open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ}
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (q : HashState p N) :
    ∀ x ∈ retainedEdges p N alpha beta gamma delta S q,
      ∀ y ∈ retainedEdges p N alpha beta gamma delta S q,
        ∀ z ∈ retainedEdges p N alpha beta gamma delta S q,
          CyclicCoordinatewiseSupported x y z →
            ∃ e ∈ retainedEdges p N alpha beta gamma delta S q,
              cyclicModeWord e 0 = cyclicModeWord x 0 ∧
              cyclicModeWord e 1 = cyclicModeWord y 1 ∧
              cyclicModeWord e 2 = cyclicModeWord z 2 := by
  classical
  intro x hx y hy z hz hsupp
  have hxRetained : Retained p N alpha beta gamma delta S q x := by
    have hx' : x ∈ edgeFinset N alpha beta gamma delta ∧
        Retained p N alpha beta gamma delta S q x := by
      simpa only [retainedEdges, Finset.mem_filter] using hx
    exact hx'.2
  have hyRetained : Retained p N alpha beta gamma delta S q y := by
    have hy' : y ∈ edgeFinset N alpha beta gamma delta ∧
        Retained p N alpha beta gamma delta S q y := by
      simpa only [retainedEdges, Finset.mem_filter] using hy
    exact hy'.2
  have hzRetained : Retained p N alpha beta gamma delta S q z := by
    have hz' : z ∈ edgeFinset N alpha beta gamma delta ∧
        Retained p N alpha beta gamma delta S q z := by
      simpa only [retainedEdges, Finset.mem_filter] using hz
    exact hz'.2
  obtain ⟨sx, hsx, hxs⟩ := hxRetained
  obtain ⟨sy, hsy, hys⟩ := hyRetained
  obtain ⟨sz, hsz, hzs⟩ := hzRetained
  have hap :
      stateHash p N alpha beta gamma delta q 0 x +
          stateHash p N alpha beta gamma delta q 1 y =
        2 * stateHash p N alpha beta gamma delta q 2 z := by
    simpa only [stateHash] using
      (mme_stothers_phi134_cyclic_affine_hash_AP
        (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2)
        x y z hsupp)
  have hlabels : sx = sz ∧ sz = sy := by
    apply hSfree sx hsx sy hsy sz hsz
    simpa only [hxs 0, hys 1, hzs 2] using hap
  obtain ⟨e, he0, he1, he2⟩ :=
    mme_stothers_phi134_cyclic_supported_mix_closure x y z hsupp
  have hvertex (i : Fin 3)
      (a b : CyclicExactEdge N alpha beta gamma delta)
      (hab : cyclicModeWord a i = cyclicModeWord b i) :
      stateHash p N alpha beta gamma delta q i a =
        stateHash p N alpha beta gamma delta q i b := by
    simp [stateHash, cyclicAffineHash, hab]
  refine ⟨e, ?_, he0, he1, he2⟩
  simp only [retainedEdges, Finset.mem_filter]
  constructor
  · simp [edgeFinset]
  · refine ⟨sx, hsx, ?_⟩
    intro i
    fin_cases i
    · exact (hvertex 0 e x he0).trans (hxs 0)
    · exact (hvertex 1 e y he1).trans
        ((hys 1).trans (hlabels.2.symm.trans hlabels.1.symm))
    · exact (hvertex 2 e z he2).trans
        ((hzs 2).trans hlabels.1.symm)

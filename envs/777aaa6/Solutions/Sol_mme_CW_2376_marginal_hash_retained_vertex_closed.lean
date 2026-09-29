-- Prove2me | solution 1 for mme_CW_2376_marginal_hash_retained_vertex_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:32:08.9341+00:00
-- url     : https://prove2.me/submissions/f072397a-df32-47e6-bcc6-f31ac323ac2b

import Definitions.Def_mme_CW_2376_marginal_hash_retained_edges
import Theorems.Thm_mme_CW_2376_modular_hash_AP_identity
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME

set_option autoImplicit false
set_option maxRecDepth 10000

/-- Hashing the full marginal-supported hypergraph into a lower-half
progression-free label set is closed under every supported mixed triple. -/
theorem solution
    (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (cw2376ProfileLength m) → ZMod p)
    (hpodd : Odd p)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    CW2376MarginalVertexClosed
      (cw2376MarginalHashRetainedEdges m p S b0 w) := by
  classical
  intro x hx y hy z hz hsupp
  simp only [cw2376MarginalHashRetainedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx hy hz
  obtain ⟨sx, hsx, hxx, _, _⟩ := hx
  obtain ⟨sy, hsy, _, hyy, _⟩ := hy
  obtain ⟨sz, hsz, _, _, hzz⟩ := hz
  have hap := mme_CW_2376_modular_hash_AP_identity hpodd b0 w
    x.1 y.1 z.1 hsupp
  rw [hxx, hyy, hzz] at hap
  obtain ⟨hxs, hsy'⟩ :=
    mme_threeAP_free_half_modulus_no_collision p S hSrange hSfree
      sx sz sy hsx hsz hsy hap
  have hregular : CW2376MarginallyRegular
      (cw2376MixedAddress x.1 y.1 z.1) := by
    intro i r
    fin_cases i
    · simpa [cw2376MixedAddress] using x.2.2 (0 : Fin 3) r
    · simpa [cw2376MixedAddress] using y.2.2 (1 : Fin 3) r
    · simpa [cw2376MixedAddress] using z.2.2 (2 : Fin 3) r
  let e : CW2376MarginalSupportedAddress m :=
    ⟨cw2376MixedAddress x.1 y.1 z.1, hsupp, hregular⟩
  refine ⟨e, ?_, rfl⟩
  simp only [cw2376MarginalHashRetainedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine ⟨sz, hsz, ?_, ?_, ?_⟩
  · calc
      cw2376XHashMod w (e.1 0) =
          cw2376XHashMod w (x.1 0) := by
            rfl
      _ = (sx : ZMod p) := hxx
      _ = (sz : ZMod p) := congrArg (fun n : ℕ => (n : ZMod p)) hxs
  · calc
      cw2376YHashMod b0 w (e.1 1) =
          cw2376YHashMod b0 w (y.1 1) := by
            rfl
      _ = (sy : ZMod p) := hyy
      _ = (sz : ZMod p) :=
        congrArg (fun n : ℕ => (n : ZMod p)) hsy'.symm
  · exact hzz

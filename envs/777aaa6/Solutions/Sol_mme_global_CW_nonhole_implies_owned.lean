-- Prove2me | solution 1 for mme_global_CW_nonhole_implies_owned
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:18:58.84767+00:00
-- url     : https://prove2.me/submissions/098a3ccf-f330-47f7-bda6-867979455c5f

import Definitions.Def_mme_global_CW_stage_data
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem solution {degree R ell k N p : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p))
    (state : (Fin (N+2) → ZMod p) × ZMod p)
    (address : Fin k → RecursiveXHash.Address degree R bounds n)
    (hinj : Function.Injective address)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (mu : Fin 3 → Cell degree R bounds → CompleteWord ell → ℕ)
    (i : Fin 3) (j : Fin k) (f : Place n → CompleteWord ell)
    (hf : f ∈ words i (address j) (mu i))
    (hn : f ∉ holes m e S state mu (address j) i) :
    GlobalCW.Owned address mu j i f := by
  have hword := (Finset.mem_filter.mp hf).2
  refine ⟨hword.1,hword.2,?_,?_⟩
  · intro hi j' hblock hcomp
    by_contra hj
    apply hn
    apply Finset.mem_filter.mpr
    refine ⟨hf,Or.inl ⟨hi,address j',hT j',hE j',?_,hblock,hcomp⟩⟩
    exact fun h ↦ hj (hinj h)
  · intro hi j' hblock hcomp
    by_contra hj
    apply hn
    apply Finset.mem_filter.mpr
    refine ⟨hf,Or.inr ⟨hi,address j',hT j',hE j',?_,hblock,hcomp⟩⟩
    exact fun h ↦ hj (hinj h)

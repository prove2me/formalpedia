-- Prove2me | Theorems.Thm_mme_global_CW_nonhole_implies_owned
-- name    : mme_global_CW_nonhole_implies_owned
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:12:33.000045+00:00
-- url     : https://prove2.me/theorems/8d8b80f4-5403-4ca4-90d8-84f95c0964d6
-- title:
--   Surviving global words satisfy sequential ownership
-- statement:
--   A global exact-profile word outside the explicitly counted compatibility holes is owned among any injectively enumerated target subfamily in the same hash buckets.
-- source:
--   Finite global extraction for More Asymmetry Proposition 5.1 and Theorem 5.3.

import Definitions.Def_mme_global_CW_stage_data
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem mme_global_CW_nonhole_implies_owned {degree R ell k N p : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
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
  sorry

-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_force_spins_fiber_card_bound
-- name    : ZeroFreeRRG.Hardcore.force_spins_fiber_card_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:08:05.196193+00:00
-- url     : https://prove2.me/theorems/4a7f28ca-2bee-43e1-a3bc-d04c89f19f95
-- title:
--   Forcing spins has bounded fiber size
-- statement:
--   For a finite set of vertices S and a finite spin set A, at most |A|^|S| configurations map to any prescribed configuration after all spins in S are forced to a fixed spin.
-- source:
--   Chunyang Wang et al., Zero-freeness for random regular graphs up to the replica symmetry breaking threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, proof of Lemma 4.20, Step 1 (supporting argument).

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.force_spins_fiber_card_bound {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
    (S : Finset V) (a₀ : A) (τ : V → A) :
    ((Finset.univ : Finset (V → A)).filter
      (fun σ => (fun v => if v ∈ S then a₀ else σ v) = τ)).card ≤
      (Fintype.card A) ^ S.card := by sorry

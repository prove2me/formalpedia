-- Prove2me | Theorems.Thm_mme_certified_entropy_bounds
-- name    : mme_certified_entropy_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T20:44:47.186133+00:00
-- url     : https://prove2.me/theorems/e8c39320-5f31-4973-8f2f-b73767e613ee
-- title:
--   Two-sided certified entropy bounds against smooth reference values
-- statement:
--   Two-sided certified bounds on Shannon entropy against a reference value, and the unnormalized form.
--
--   For a nonnegative weight `p` and any positive reference `q`, the Gibbs inequality gives
--   `p - p^2/q - p log q <= -p log p <= q - p - p log q`. Summing over the alphabet bounds the entropy
--   of `p` between two expressions that involve `p` rationally plus the single transcendental quantity
--   `log q`. Choosing every reference of the form `2^a 3^b 5^c 7^d` makes each `log q` an integer
--   combination of `log 2`, `log 3`, `log 5` and `log 7`, so a rigorous rational enclosure of those four
--   constants turns the bounds into a finite exact-arithmetic computation. Taking each reference close
--   to its own weight makes the gap between the two bounds as small as desired.
--
--   The last part records that the unnormalized entropy of a family of masses is the total mass times
--   the entropy of the normalized distribution.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_entropy_reference
open BigOperators MME MME.RegionRate MME.Cert
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_certified_entropy_bounds :
    (∀ {W : Type u} [Fintype W] (p : W → ℝ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      ∑ w, (p w - (p w) ^ 2 / qval (e w) - p w * Real.log (qval (e w))) ≤ entropy p) ∧
    (∀ {W : Type u} [Fintype W] (p : W → ℝ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      entropy p ≤ ∑ w, (qval (e w) - p w - p w * Real.log (qval (e w)))) ∧
    ∀ {W : Type u} [Fintype W] (x : W → ℝ), 0 < ∑ w, x w →
      massEntropy x = (∑ w, x w) * entropy (fun w ↦ x w / (∑ w, x w)) := by sorry

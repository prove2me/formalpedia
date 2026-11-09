-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_flag_singleton_bound
-- name    : WitnessIsolation.AffineCollapse.flag_singleton_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:50.529574+00:00
-- url     : https://prove2.me/theorems/44bfe658-081d-428b-b083-00626f9f4b39
-- title:
--   Lemma 5.2 — Flag lemma
-- statement:
--   Let T be any subset of the t-dimensional binary cube, and let z be uniform in that cube. For 0≤j≤t, let F_j consist of points agreeing with z in all coordinates after j. Then
--
--   $$\sum_{j=0}^t\Pr[|T\cap F_j|=1]<2.$$
--
--   The sum contains both endpoints and the inequality is strict. Empty T and t=0 are included. The estimate supplies the reference singleton bound for product regions.
--
--   Differences from the source:
--   - encoding: coordinates numbered 1,…,t and condition i>j → coordinates numbered 0,…,t−1 and condition j≤i; reason: these are precisely the same flags, including F₀ and F_t
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Lemma 5.2, printed p. 10, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_regions

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Lemma 5.2, all t+1 levels and the strict bound, including t=0. -/
theorem flag_singleton_bound (t : ℕ) (T : Finset (Bits t)) :
    ∑ j ∈ Finset.range (t+1), uniformProb (fun z : Bits t => (T ∩ flag z j).card = 1) < 2 := by sorry

end WitnessIsolation.AffineCollapse

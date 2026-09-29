-- Prove2me | Theorems.Thm_mme_sixSymmetrization_uniform_bigAdd_isomorphic
-- name    : mme_sixSymmetrization_uniform_bigAdd_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T16:57:43.850987+00:00
-- url     : https://prove2.me/theorems/7be33813-9bf0-4d01-b2d2-90bb60e1e468
-- title:
--   Six-symmetrizing a uniform direct sum of k copies gives k^6 copies
-- statement:
--   For a tensor $T$ over a field $K$ and a natural number $k$,
--
--   $$\mathrm{sym}_6\Big(\bigoplus_{i<k} T\Big) \;\cong\; \bigoplus_{j<k^6} \mathrm{sym}_6(T).$$
--
--   The six-symmetrization is the Kronecker product of six permuted copies of its argument — three cyclic rotations, and the same three after swapping the first two modes. Applying it to a direct sum of $k$ identical summands and expanding the product of six $k$-fold sums gives $k^6$ terms, each a Kronecker product of six permuted copies of $T$, that is, a copy of $\mathrm{sym}_6(T)$.
--
--   The statement is an isomorphism, not merely a restriction in one direction, so it may be used to move copies in or out of a symmetrization. It is the six-mode analogue of the corresponding cyclic fact, and it is what converts "an extraction produced $k$ copies of a family" into "its six-symmetrization contains $k^6$ copies of the symmetrized family", the form in which copy counts enter a $\tau$-value bound.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm

open MME MME.TensorObj

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_uniform_bigAdd_isomorphic {K : Type u} [Field K] (T : TensorObj K 3) (k : ℕ) :
    Isomorphic (sixSymmetrization (bigAdd (fun _ : Fin k ↦ T)))
      (bigAdd (fun _ : Fin (k ^ 6) ↦ sixSymmetrization T)) := by sorry

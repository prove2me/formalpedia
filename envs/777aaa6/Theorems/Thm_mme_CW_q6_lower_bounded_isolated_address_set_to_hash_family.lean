-- Prove2me | Theorems.Thm_mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
-- name    : mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:16:47.782173+00:00
-- url     : https://prove2.me/theorems/28a58796-bc65-45a8-afb8-da7f6d1b992c
-- title:
--   Lower-bounded isolated q=6 fibers admit common-H extraction
-- statement:
--   Fix exact q=6 coupled addresses and finite families $F\subseteq E$. Assume $F$ is isolated relative to $E$ in the X and Y modes, every represented Z-address has at least the same positive multiplicity $H$, and every coordinatewise-supported mix of three retained modes is realized by an ambient address in $E$. Then the retained Z-label set supports a primary hash family with exactly $H$ entries per label:\n\n$$\nA=|z(F)|,\qquad \operatorname{Nonempty}(\mathrm{PrimaryHashFamily}(N,L,G,A,H)).\n$$\n\nThe result truncates each positive Z-fiber to a common size without discarding any Z-label. It preserves the shared Z multiplicity required for C-tensors; it does not prune Z-collisions or force $H=1$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), common positive Z-multiplicity extraction for C-tensors on journal p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_finset_uniform_positive_fiber_truncation
import Theorems.Thm_mme_CW_q6_uniform_isolated_address_set_to_hash_family

open MME

theorem mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
    (N L G H : ℕ)
    (E F : Finset (CWQ6ExactCoupledAddress N L G))
    (hH : 0 < H)
    (hFE : F ⊆ E)
    (hisolated : ∀ e ∈ F, ∀ e' ∈ E,
      (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e')
    (hmin : ∀ c ∈ F.image (fun e => e.1 2),
      H ≤ (F.filter (fun e => e.1 2 = c)).card)
    (hclosed : ∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
      ∃ e' ∈ E,
        e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2) :
    Nonempty (CWQ6PrimaryHashFamily N L G
      (F.image (fun e => e.1 2)).card H) := by sorry

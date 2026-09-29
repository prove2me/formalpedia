-- Prove2me | Theorems.Thm_mme_CW_q6_uniform_isolated_address_set_to_hash_family
-- name    : mme_CW_q6_uniform_isolated_address_set_to_hash_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:11:27.194495+00:00
-- url     : https://prove2.me/theorems/bc4abb90-4b03-46c3-b55c-07d999a947de
-- title:
--   Uniform isolated q=6 addresses form a primary hash family
-- statement:
--   Fix exact q=6 coupled Coppersmith--Winograd addresses of parameters $(N,L,G)$. Let $F\subseteq E$ be finite families such that every retained address is isolated, relative to all of $E$, in each of the X and Y modes. Suppose every represented Z-address occurs exactly $H>0$ times in $F$. Finally, assume closure: whenever the X-mode of one retained address, the Y-mode of another, and the Z-mode of a third are coordinatewise supported together, those three modes occur together on an ambient address in $E$. Then the retained addresses admit a canonical enumeration as a primary hash family with\n\n$$\nA=|z(F)| \quad\text{and}\quad H\text{ entries per Z-fiber}.\n$$\n\nThus finite X/Y collision isolation, exact common Z-multiplicity, and ambient closure are sufficient for the combinatorial induced-family certificate. The statement deliberately makes no identification of fine tensor factors across different addresses.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), first-hash collision deletion and C-tensor grouping on journal pp. 260--261 and 270--271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

theorem mme_CW_q6_uniform_isolated_address_set_to_hash_family
    (N L G H : ℕ)
    (E F : Finset (CWQ6ExactCoupledAddress N L G))
    (hH : 0 < H)
    (hFE : F ⊆ E)
    (hisolated : ∀ e ∈ F, ∀ e' ∈ E,
      (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e')
    (huniform : ∀ c ∈ F.image (fun e => e.1 2),
      (F.filter (fun e => e.1 2 = c)).card = H)
    (hclosed : ∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
      ∃ e' ∈ E,
        e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2) :
    Nonempty (CWQ6PrimaryHashFamily N L G
      (F.image (fun e => e.1 2)).card H) := by sorry

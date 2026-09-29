-- Prove2me | Theorems.Thm_mme_CW_2376_exact_profile_address_marginals
-- name    : mme_CW_2376_exact_profile_address_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:38:26.750923+00:00
-- url     : https://prove2.me/theorems/3481c558-cb2b-4445-bb66-cca575808dbe
-- title:
--   Exact marginal counts of the CW 2.376 profile
-- statement:
--   Let an exact CW 2.376 profile address have length $3{,}000{,}000m$ and the fifteen prescribed joint-type multiplicities from the optimized squared Coppersmith--Winograd profile.  In each of its three modes, the five grade fibers have exactly the same cardinalities:
--
--   $$
--   (384072m,\;1308290m,\;1231903m,\;75036m,\;699m).
--   $$
--
--   This is the concrete marginal-incidence identity needed by the outer hashing and collision-pruning argument: it converts the joint profile into the five per-mode multinomial counts used to enumerate address words.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), optimized squared-tensor profile in equation (13), journal pp. 267--268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_induced_family

open MME BigOperators

theorem mme_CW_2376_exact_profile_address_marginals
    (m : ℕ) (a : CW2376ExactProfileAddress m) :
    ∀ i : Fin 3,
      (Finset.univ.filter (fun j => a.1 i j = (0 : Fin 5))).card =
          384072 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (1 : Fin 5))).card =
          1308290 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (2 : Fin 5))).card =
          1231903 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (3 : Fin 5))).card =
          75036 * m ∧
      (Finset.univ.filter (fun j => a.1 i j = (4 : Fin 5))).card =
          699 * m := by
  sorry

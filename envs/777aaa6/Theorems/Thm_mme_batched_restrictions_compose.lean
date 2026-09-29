-- Prove2me | Theorems.Thm_mme_batched_restrictions_compose
-- name    : mme_batched_restrictions_compose
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:40:23.641973+00:00
-- url     : https://prove2.me/theorems/01a1fe62-0a02-4b7d-855e-59df759e445b
-- title:
--   Compose recursive extractions with exact input and output copy counts
-- statement:
--   If c copies of B restrict from r copies of A, and d copies of C restrict from s copies of B, then c*d copies of C restrict from r*s copies of A. The result keeps all output copies and charges the complete input-copy overhead, without a positivity condition or floor approximation.
-- source:
--   Finite algebraic ingredients for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3, Theorem 6.4, and Sections 6.5–6.6. These statements retain explicit finite hole budgets and type-copy overheads; they do not assert the entropy asymptotics or numerical certificate.

import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested

open MME MME.TensorObj BigOperators
universe u
set_option autoImplicit false

theorem mme_batched_restrictions_compose {K : Type u} [Field K] (A B C : TensorObj K 3)
    (r s c d : ℕ)
    (hAB : Restrict (bigAdd (fun _ : Fin c ↦ B)) (bigAdd (fun _ : Fin r ↦ A)))
    (hBC : Restrict (bigAdd (fun _ : Fin d ↦ C)) (bigAdd (fun _ : Fin s ↦ B))) :
    Restrict (bigAdd (fun _ : Fin (c * d) ↦ C))
      (bigAdd (fun _ : Fin (r * s) ↦ A)) := by sorry

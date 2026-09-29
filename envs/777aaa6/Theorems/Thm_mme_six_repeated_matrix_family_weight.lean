-- Prove2me | Theorems.Thm_mme_six_repeated_matrix_family_weight
-- name    : mme_six_repeated_matrix_family_weight
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:50:07.884418+00:00
-- url     : https://prove2.me/theorems/95043d54-f6b2-4f36-8d88-42ed4b764958
-- title:
--   Parent and child matrix extractions compose with exact sixth-power multiplicity
-- statement:
--   If p copies of Y restrict from X, and a q-term matrix family restricts from the six-fold symmetrization of Y with weight at least exp(rate), then a flattened p^6*q-term matrix family restricts from the six-fold symmetrization of X with weight at least p^6*exp(rate). All matrix dimensions are retained from the child family. The theorem is valid over every field, for every real tau and rate, including zero multiplicities; it assumes the parent and child restrictions explicitly.
-- source:
--   Exact tensor direct-sum multiplicity under six-symmetrization and restriction composition.

import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
open MME BigOperators
set_option autoImplicit false
universe u

theorem mme_six_repeated_matrix_family_weight
    {K : Type u} [Field K] {p q : ℕ} {X Y : TensorObj K 3}
    (a b c : Fin q → ℕ) (tau rate : ℝ)
    (hparent : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin p => Y)) X)
    (hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization Y))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun r : Fin (p ^ 6 * q) =>
        let j := (finProdFinEquiv.symm r).2
        MMObj K (a j) (b j) (c j))) (sixSymmetrization X) ∧
    (p : ℝ) ^ 6 * Real.exp rate ≤
      ∑ r : Fin (p ^ 6 * q),
        let j := (finProdFinEquiv.symm r).2
        ((a j * b j * c j : ℕ) : ℝ) ^ tau := by sorry

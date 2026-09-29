-- Prove2me | Theorems.Thm_bernoulli_product_measure_coords_indep
-- name    : bernoulli_product_measure_coords_indep
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T03:24:04.399716+00:00
-- url     : https://prove2.me/theorems/6b3d8fbd-04d9-472c-ab88-d294dc53c673
-- statement:
--   Coordinate independence of the product-Bernoulli sampling measure. The family of per-coordinate Bool indicators $(\omega \mapsto \omega(w))_{w}$ is `iIndepFun` (mutually independent) under `bernMeasure p` = `Measure.pi` of independent Bernoulli$(p)$ coordinates on $(\mathrm{Fin}\,n_1 \times \mathrm{Fin}\,n_2) \to \mathrm{Bool}$. Together with the keystone bridge (bernoulliExpectation = integral against `bernMeasure`), this exposes the powerset sampling model's coordinate independence in Mathlib's stock `ProbabilityTheory.iIndepFun` form, so Mathlib's independence API (product of expectations, independent sums, condExp w.r.t. coordinate sub-sigma-algebras, Hoeffding/sub-Gaussian MGF) applies directly. Proof: `iIndepFun_pi` (coordinates of a `Measure.pi` are independent).
-- source:
--   Mathlib Probability.Independence.Basic (iIndepFun_pi). Candes-Recht 2009 arXiv:0805.4471 section 6 (independent Bernoulli sampling).

import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.Probability.Independence.Basic
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

theorem bernoulli_product_measure_coords_indep
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1) :
    iIndepFun (fun (w : Fin n1 × Fin n2) (ω : (Fin n1 × Fin n2) → Bool) => ω w)
      (bernMeasure p hp) := by sorry

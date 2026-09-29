-- Prove2me | solution 1 for mme_released_joint_outer_inner_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:21:43.478014+00:00
-- url     : https://prove2.me/submissions/1f95f398-9baa-4505-8070-aee8057e7904

import Theorems.Thm_mme_released_global_simultaneous_uniform_window_extraction
import Theorems.Thm_mme_permuted_product_extraction_six_matrix_weight_rate
import Definitions.Def_mme_released_joint_interior_profiles

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal
  MME.MoreAsymmetryExactSeed MME.GlobalCW
open MME.ReleasedJointInterior (roleEquiv)
universe u

/-- A matrix family in the joint outer window product composes with all six
outer extractions, retaining every source multiplicity and outer copy rate. -/
theorem solution
    {K : Type u} [Field K] (rho : Fin 6 → ℝ)
    (hrho : ∀ owner, 0 ≤ rho owner)
    (hgap : ∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∃ k0 : ℕ,
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ k : ℕ, k0 ≤ k →
      ∀ tau rate : ℝ,
      (∀ (hk : 0 < k ^ 2) (reference : ∀ owner, Reference owner (k ^ 2)),
        ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
          Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (sixSymmetrization (kronFin 6 (fun owner =>
              permObj (roleEquiv owner) (tensor K
                ((frame owner (k ^ 2) hk (reference owner)).window
                  (windowGood owner (k ^ 2) eps)))))) ∧
          Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) →
      ∃ (inputs : Fin 6 → ℕ) (q : ℕ) (a b c : Fin q → ℕ),
        (∀ owner, 1 ≤ inputs owner) ∧
        (∀ owner, inputs owner ≤ (blocks (k ^ 2) + 1) ^ 10935) ∧ 0 < q ∧
        Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j)))
          (sixSymmetrization (kronFin 6 (fun owner => permObj (roleEquiv owner)
            (bigAdd (fun _ : Fin (inputs owner) =>
              tensor K (fun _ (_ : FineWord (4 * blocks (k ^ 2))) => True)))))) ∧
        Real.exp (6 * (∑ owner,
          (rho owner * (blocks (k ^ 2) : ℝ) + Real.log (inputs owner : ℝ))) + rate) ≤
          ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau := by
  classical
  obtain ⟨eps0, heps0, k0, houter⟩ :=
    mme_released_global_simultaneous_uniform_window_extraction
      (K := K) rho hrho hgap
  refine ⟨eps0, heps0, k0, ?_⟩
  intro eps heps hepsbound k hk tau rate hinner
  choose hk2 reference S hinputs hpoly hrate hrestrict using
    houter eps heps hepsbound k hk
  obtain ⟨q, a, b, c, hq, hchild, hweight⟩ := hinner (hk2 0) reference
  have hcount (owner : Fin 6) : Real.exp
      (rho owner * (blocks (k ^ 2) : ℝ) + Real.log ((S owner).inputs : ℝ)) ≤
      (⌈Real.exp (S owner).rate⌉₊ : ℝ) :=
    (Real.exp_le_exp.mpr (hrate owner)).trans (Nat.le_ceil _)
  obtain ⟨q', a', b', c', hq', hrestrict', hweight'⟩ :=
    mme_permuted_product_extraction_six_matrix_weight_rate
      (fun owner => bigAdd (fun _ : Fin (S owner).inputs =>
        tensor K (fun _ (_ : FineWord (4 * blocks (k ^ 2))) => True)))
      (fun owner => tensor K ((frame owner (k ^ 2) (hk2 owner) (reference owner)).window
        (windowGood owner (k ^ 2) eps)))
      (fun owner => ⌈Real.exp (S owner).rate⌉₊) roleEquiv
      (fun owner => rho owner * (blocks (k ^ 2) : ℝ) +
        Real.log ((S owner).inputs : ℝ))
      a b c hq tau rate hrestrict hcount hchild hweight
  exact ⟨(fun owner => (S owner).inputs), q', a', b', c',
    hinputs, hpoly, hq', hrestrict', hweight'⟩


#print axioms solution

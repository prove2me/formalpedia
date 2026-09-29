-- Prove2me | solution 1 for PGLQuotient.summable_pi_geom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:24:19.231148+00:00
-- url     : https://prove2.me/submissions/739a346b-d923-4626-950f-cead31d887a1

-- Sol generated from Algebra/PGLQuotient/HeightThreshold.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel

/-!
# Integrability threshold for the lattice-minima height

Let `α` be the homothety-invariant normalised lattice-minima height on the standard
arithmetic quotient of the Bruhat–Tits building of `PGL_d(F_q((t^{-1})))`, modelled as in
`Algebra.PGLQuotient.VertexModel`.

The main theorem of this file is the *exact integrability threshold*

`Summable (fun g => vertexWeight q g * α g ^ s) ↔ s < d`,

i.e. `α ∈ L^r` precisely for `r < d` (in particular for `0 < r < d`).  The positive direction
is proved by factoring the majorant into a product of `d-1` independent geometric series over
the gap coordinates; the negative direction uses the cusp ray `λ = (n,0,…,0)`, along which the
mass decays exactly like `α^{-d}`.
-/

open PGLQuotient

open Finset





variable {d : ℕ} {q : ℝ}

















open PGLQuotient in
theorem solution: ∀ {m : ℕ} (x : Fin m → ℝ), (∀ k, 0 ≤ x k) → (∀ k, x k < 1) →
    Summable (fun h : Fin m → ℕ => ∏ k, x k ^ h k) ∧
      ∑' h : Fin m → ℕ, ∏ k, x k ^ h k = ∏ k, (1 - x k)⁻¹ := by
  intro m
  induction m with
  | zero =>
      intro x _ _
      refine ⟨Summable.of_finite, ?_⟩
      simp
  | succ m ih =>
      intro x h0 h1
      obtain ⟨hs2, hv2⟩ := ih (fun k => x k.succ) (fun k => h0 _) (fun k => h1 _)
      have hsum1 : Summable (fun n : ℕ => x 0 ^ n) :=
        summable_geometric_of_lt_one (h0 0) (h1 0)
      have hnn1 : (0 : ℕ → ℝ) ≤ fun n : ℕ => x 0 ^ n := fun n => pow_nonneg (h0 0) n
      have hnn2 : (0 : (Fin m → ℕ) → ℝ) ≤ fun h : Fin m → ℕ => ∏ k : Fin m, x k.succ ^ h k :=
        fun h => Finset.prod_nonneg (fun k _ => pow_nonneg (h0 _) _)
      have hprod := hsum1.mul_of_nonneg hs2 hnn1 hnn2
      have key : ∀ p : ℕ × (Fin m → ℕ),
          (∏ k : Fin (m+1), x k ^ ((Fin.consEquiv (fun _ => ℕ)) p) k)
            = x 0 ^ p.1 * ∏ k : Fin m, x k.succ ^ p.2 k := by
        intro p
        rw [Fin.prod_univ_succ]
        simp [Fin.consEquiv_apply]
      have hcomp : Summable (fun p : ℕ × (Fin m → ℕ) =>
          ∏ k : Fin (m+1), x k ^ ((Fin.consEquiv (fun _ => ℕ)) p) k) := by
        simpa only [key] using hprod
      have hsummable : Summable (fun h : Fin (m+1) → ℕ => ∏ k, x k ^ h k) :=
        (Equiv.summable_iff (Fin.consEquiv (fun _ => ℕ))).mp hcomp
      refine ⟨hsummable, ?_⟩
      have hval : ∑' h : Fin (m+1) → ℕ, ∏ k, x k ^ h k
          = ∑' p : ℕ × (Fin m → ℕ), x 0 ^ p.1 * ∏ k : Fin m, x k.succ ^ p.2 k := by
        rw [← (Fin.consEquiv (fun _ => ℕ)).tsum_eq (fun h : Fin (m+1) → ℕ => ∏ k, x k ^ h k)]
        exact tsum_congr key
      have hslice : ∀ b : ℕ, Summable
          (fun c : Fin m → ℕ => x 0 ^ b * ∏ k : Fin m, x k.succ ^ c k) := fun b => hs2.mul_left _
      rw [hval, hprod.tsum_prod' hslice]
      rw [tsum_congr (fun n : ℕ => hs2.tsum_mul_left (x 0 ^ n)), tsum_mul_right, hv2,
        tsum_geometric_of_lt_one (h0 0) (h1 0), Fin.prod_univ_succ]

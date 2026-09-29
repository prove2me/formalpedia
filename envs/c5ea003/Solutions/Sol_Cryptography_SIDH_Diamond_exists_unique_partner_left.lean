-- Prove2me | solution 1 for Cryptography.SIDH.Diamond.exists_unique_partner_left
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:27:54.170966+00:00
-- url     : https://prove2.me/submissions/943e383e-77d0-48e0-8806-831741194b15

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma

open Cryptography.SIDH Diamond in
theorem solution {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] (D : Diamond E₁ E₂ E₃ E₄)
    (hab : Nat.Coprime D.a D.b) {x : E₁}
    (hx : (D.N : ℤ) • x = 0) : ∃! y : E₄, D.kani (x, y) = 0 := by
  obtain ⟨u, v, huv⟩ := D.exists_inv_a hab
  -- a point of `E₂` killed by `a` and by `N` is zero (Bézout)
  have hkill : ∀ Q : E₂, (D.a : ℤ) • Q = 0 → (D.N : ℤ) • Q = 0 → Q = 0 := by
    intro Q haQ hNQ
    have e : (1 : ℤ) = u * D.a - v * D.N := by linear_combination (-1 : ℤ) * huv
    calc Q = (1 : ℤ) • Q := (one_zsmul Q).symm
      _ = (u * D.a - v * D.N) • Q := by rw [← e]
      _ = u • ((D.a : ℤ) • Q) - v • ((D.N : ℤ) • Q) := by rw [sub_smul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [haQ, hNQ, smul_zero, smul_zero, sub_zero]
  -- existence: the graph point over `u • φ x`
  have hQ : (D.N : ℤ) • (u • D.phi x) = 0 := by
    rw [smul_comm, ← map_zsmul, hx, map_zero, smul_zero]
  have hxx : D.phiHat (u • D.phi x) = x := by
    rw [map_zsmul, D.phiHat_phi, smul_smul, mul_comm u (D.a : ℤ)]
    exact zsmul_eq_self_of_one_add hx ⟨v, huv⟩
  have hker : D.kani (x, D.psi' (u • D.phi x)) = 0 := by
    have h := D.kani_graph hQ
    rwa [graphMap_apply, hxx] at h
  refine ⟨D.psi' (u • D.phi x), hker, fun y hy => ?_⟩
  -- uniqueness: a kernel point with zero first coordinate is zero
  have hdiff : D.kani ((0 : E₁), y - D.psi' (u • D.phi x)) = 0 := by
    have e : ((0 : E₁), y - D.psi' (u • D.phi x)) = (x, y) - (x, D.psi' (u • D.phi x)) := by
      ext <;> simp
    rw [e, map_sub, hy, hker, sub_zero]
  obtain ⟨Q, hNQ, hz⟩ := (D.mem_ker_kani_iff hab _).1 hdiff
  rw [graphMap_apply, Prod.mk.injEq] at hz
  have haQ : (D.a : ℤ) • Q = 0 := by rw [← D.phi_phiHat, ← hz.1, map_zero]
  rw [hkill Q haQ hNQ, map_zero, map_zero, sub_eq_zero] at hz
  exact hz.2

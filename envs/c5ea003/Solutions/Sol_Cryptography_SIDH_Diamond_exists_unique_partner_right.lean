-- Prove2me | solution 1 for Cryptography.SIDH.Diamond.exists_unique_partner_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:32:25.482552+00:00
-- url     : https://prove2.me/submissions/9af4890d-9476-450e-b411-b7f67e97b94b

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma

open Cryptography.SIDH Diamond in
theorem solution {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] (D : Diamond E₁ E₂ E₃ E₄)
    (hab : Nat.Coprime D.a D.b) {y : E₄}
    (hy : (D.N : ℤ) • y = 0) : ∃! x : E₁, D.kani (x, y) = 0 := by
  -- Bézout for `b` against `N = a + b`
  have hbN : Nat.Coprime D.b D.N := by
    show Nat.Coprime D.b (D.a + D.b)
    exact Nat.coprime_add_self_right.2 hab.symm
  obtain ⟨p, q, hpq⟩ := Nat.Coprime.isCoprime hbN
  have hkill : ∀ Q : E₂, (D.b : ℤ) • Q = 0 → (D.N : ℤ) • Q = 0 → Q = 0 := by
    intro Q hbQ hNQ
    calc Q = (1 : ℤ) • Q := (one_zsmul Q).symm
      _ = (p * D.b + q * D.N) • Q := by rw [hpq]
      _ = p • ((D.b : ℤ) • Q) + q • ((D.N : ℤ) • Q) := by rw [add_smul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hbQ, hNQ, smul_zero, smul_zero, add_zero]
  -- existence: the graph point over `p • ψ'^ y`
  have hQ : (D.N : ℤ) • (p • D.psi'Hat y) = 0 := by
    rw [smul_comm, ← map_zsmul, hy, map_zero, smul_zero]
  have hyy : D.psi' (p • D.psi'Hat y) = y := by
    rw [map_zsmul, D.psi'_psi'Hat, smul_smul]
    exact zsmul_eq_self_of_one_add hy ⟨-q, by linear_combination hpq⟩
  have hker : D.kani (D.phiHat (p • D.psi'Hat y), y) = 0 := by
    have h := D.kani_graph hQ
    rwa [graphMap_apply, hyy] at h
  refine ⟨D.phiHat (p • D.psi'Hat y), hker, fun x hx => ?_⟩
  -- uniqueness: a kernel point with zero second coordinate is zero
  have hdiff : D.kani (x - D.phiHat (p • D.psi'Hat y), (0 : E₄)) = 0 := by
    have e : (x - D.phiHat (p • D.psi'Hat y), (0 : E₄))
        = (x, y) - (D.phiHat (p • D.psi'Hat y), y) := by
      ext <;> simp
    rw [e, map_sub, hx, hker, sub_zero]
  obtain ⟨Q, hNQ, hz⟩ := (D.mem_ker_kani_iff hab _).1 hdiff
  rw [graphMap_apply, Prod.mk.injEq] at hz
  have hbQ : (D.b : ℤ) • Q = 0 := by rw [← D.psi'Hat_psi', ← hz.2, map_zero]
  rw [hkill Q hbQ hNQ, map_zero, sub_eq_zero] at hz
  exact hz.1

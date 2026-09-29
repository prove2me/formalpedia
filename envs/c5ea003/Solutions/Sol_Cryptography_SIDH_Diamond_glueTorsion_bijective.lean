-- Prove2me | solution 1 for Cryptography.SIDH.Diamond.glueTorsion_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:39:41.064179+00:00
-- url     : https://prove2.me/submissions/359fee1c-d9bf-48a0-866b-9149a05acd1e

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma

open Cryptography.SIDH Diamond in
theorem solution {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] (D : Diamond E₁ E₂ E₃ E₄)
    (hab : Nat.Coprime D.a D.b) {u : ℤ}
    (hu : ∃ v : ℤ, (D.a : ℤ) * u = 1 + (D.N : ℤ) * v) :
    Function.Bijective (D.glueTorsion u) := by
  obtain ⟨v, hv⟩ := hu
  -- `b` is invertible modulo `N = a + b`
  have hcop : Nat.Coprime D.b D.N := by
    show Nat.Coprime D.b (D.a + D.b)
    exact Nat.coprime_add_self_right.2 hab.symm
  obtain ⟨w, t, hwt⟩ := Nat.isCoprime_iff_coprime.2 hcop
  -- the composite scalar is `≡ 1 (mod N)`
  have hs : w * u * D.b * D.a = 1 + (D.N : ℤ) * (v - t - t * D.N * v) := by
    linear_combination ((D.b : ℤ) * w) * hv + (1 + (D.N : ℤ) * v) * hwt
  have hs' : u * w * D.a * D.b = 1 + (D.N : ℤ) * (v - t - t * D.N * v) := by
    linear_combination ((D.b : ℤ) * w) * hv + (1 + (D.N : ℤ) * v) * hwt
  -- the explicit inverse `y ↦ w • φ^(ψ'^ y)` on `N`-torsion
  let g : nTorsion E₄ D.N → nTorsion E₁ D.N := fun y =>
    ⟨w • D.phiHat (D.psi'Hat y.1), by
      have hy : (D.N : ℤ) • y.1 = 0 := y.2
      show (D.N : ℤ) • (w • D.phiHat (D.psi'Hat y.1)) = 0
      have h0 : (D.N : ℤ) • D.psi'Hat y.1 = 0 := by
        rw [← map_zsmul, hy, map_zero]
      rw [smul_comm, ← map_zsmul D.phiHat, h0, map_zero, smul_zero]⟩
  refine Function.bijective_iff_has_inverse.2 ⟨g, fun x => ?_, fun y => ?_⟩
  · have hx : (D.N : ℤ) • x.1 = 0 := x.2
    apply Subtype.ext
    show w • D.phiHat (D.psi'Hat (u • D.psi' (D.phi x.1))) = x.1
    rw [map_zsmul, D.psi'Hat_psi', map_zsmul, map_zsmul, D.phiHat_phi, smul_smul, smul_smul,
      smul_smul, hs, add_smul, one_smul, mul_comm, mul_smul, hx, smul_zero, add_zero]
  · have hy : (D.N : ℤ) • y.1 = 0 := y.2
    apply Subtype.ext
    show u • D.psi' (D.phi (w • D.phiHat (D.psi'Hat y.1))) = y.1
    rw [map_zsmul, D.phi_phiHat, map_zsmul, map_zsmul, D.psi'_psi'Hat, smul_smul, smul_smul,
      smul_smul, hs', add_smul, one_smul, mul_comm, mul_smul, hy, smul_zero, add_zero]

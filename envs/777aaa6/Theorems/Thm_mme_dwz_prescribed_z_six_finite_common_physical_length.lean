-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_six_finite_common_physical_length
-- name    : mme_dwz_prescribed_z_six_finite_common_physical_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T07:15:49.472803+00:00
-- url     : https://prove2.me/theorems/92844010-8c47-4d0e-aca7-e7ea324e6633
-- title:
--   Finite prescribed-Z families have actual witnesses at common physical lengths
-- statement:
--   Consider a finite family of tensors over one field, with component-dependent Z bases, grade alphabets, and integer split profiles $p_i$. Their positive denominators $D_i$ may differ. Suppose each has a prescribed-Z six-symmetric restriction-value certificate at $V_i$, and choose $0<v_i<V_i$. There is one positive integer $L_0$ such that, for every nonnegative integer $r$ and every component $i$, an index $m_i$ satisfies
--
--   $$D_i m_i=L_0r,$$
--
--   and an actual finite matrix-multiplication direct sum restricts from the six-symmetrization of its prescribed-Z tensor at that index, with total $\tau$-weight at least $v_i^{6L_0r}$. Thus both the physical tensor length and the weight normalization are common across components. The theorem includes an empty family and $r=0$. It does not assume that independently frequent sets of indices intersect.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Definitions 3.7 and 3.9 (printed pp. 22–23) and Equation (3) (printed p. 24). Finite common-length synchronization of the prescribed-Z restriction-witness interface, using exact finite witness powering; no new numerical component-value premise or limsup-equivalence assertion.

import Definitions.Def_mme_dwz_prescribed_z_split_value

set_option autoImplicit false

universe u w

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module

theorem mme_dwz_prescribed_z_six_finite_common_physical_length
    {K : Type u} [Field K] {J : Type w} [Fintype J]
    (T : J → TensorObj K 3) {ι : J → Type u} {t : J → ℕ}
    (bZ : (i : J) → Basis (ι i) K ((T i).V 2))
    (grade : (i : J) → ι i → Fin (t i))
    (p : (i : J) → IntegerZSplitProfile (t i))
    (tau : ℝ) (V v : J → ℝ)
    (hpos : ∀ i, 0 < v i) (hstrict : ∀ i, v i < V i)
    (hvalue : ∀ i, HasPrescribedZSixRestrictionValueAtLeast
      (T i) (bZ i) (grade i) (p i) tau (V i)) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (r : ℕ) (i : J), ∃ m : ℕ,
      (p i).length m = L₀ * r ∧
      SixFiniteWitness TensorObj.Restrict
        (prescribedZPower (T i) (bZ i) (grade i) (p i) m)
        (L₀ * r) tau (v i) := by sorry

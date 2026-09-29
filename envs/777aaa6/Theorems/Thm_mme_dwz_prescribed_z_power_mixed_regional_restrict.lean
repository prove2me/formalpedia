-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_power_mixed_regional_restrict
-- name    : mme_dwz_prescribed_z_power_mixed_regional_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T10:13:48.125625+00:00
-- url     : https://prove2.me/theorems/a0b00b68-d41a-4f60-93d3-34ef8de9e4f5
-- title:
--   Exact mixed regional profiles restrict a prescribed-Z tensor power
-- statement:
--   Let $K$ be a field, $T$ a trilinear tensor with chosen mode bases, and $g$ a grading of its chosen Z basis by $[t]=\{0,\ldots,t-1\}$. Let $p$ be an integer split profile with positive denominator $D$ and counts $p_a$ summing to $D$. For every region $r\in[k]$, let $p^{(r)}$ have positive denominator $D_r$ and counts $p^{(r)}_a$ summing to $D_r$. Choose nonnegative integers $m,m_r$ satisfying the exact length and count identities
--   $$
--   Dm=\sum_{r<k}D_rm_r,\qquad
--   p_am=\sum_{r<k}p^{(r)}_am_r\quad(a\in[t]).
--   $$
--   Write $T^{\otimes Dm}[p]$ for the actual Z-coordinate projection retaining precisely those canonical power-basis words with $p_am$ occurrences of each grade $a$. Then there is a mode-wise linear tensor restriction
--   $$
--   T^{\otimes Dm}[p]\longrightarrow
--   \bigotimes_{r<k}T^{\otimes D_rm_r}[p^{(r)}].
--   $$
--   The product is ordered by the full region labels. Arbitrary finite numbers of regions, zero regional lengths, and the empty product are included. No positivity of a grade fiber, coefficient-support assumption, or pre-existing realization map is required.
--
--   For positive fourth-level CW components, the case $k=3$ is the exact finite regional parent-profile restriction needed before changing orientations in the recursive construction. The conclusion is an actual tensor restriction, not a scalar value inequality. It does not establish child-component extraction, typical-block mass, entropy estimates, or a parent endpoint.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 (28 November 2023), Section 7, Claim 7.1 and its proof, https://arxiv.org/html/2210.10173v5#S7. This is the exact denominator-cleared finite restriction, generalized from three ordered regions to any finite number. The underlying prescribed-splitting projection follows Definition 3.9. The proved same-profile binary special case is Prove2Me theorem 0844ed73-f692-4bb2-9f91-5df213fdfc53; the proof here constructs the arbitrary mixed-profile regional maps rather than treating that same-profile case as sufficient.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open PiTensorProduct TensorProduct BigOperators
open MME.TensorObj
open scoped Classical

universe u

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_dwz_prescribed_z_power_mixed_regional_restrict
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    {t k : ℕ} (grade : I 2 → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ)
    (region : Fin k → IntegerZSplitProfile t) (multiple : Fin k → ℕ)
    (hlength : p.length m = ∑ r, (region r).length (multiple r))
    (hcounts : ∀ a, p.count a * m =
      ∑ r, (region r).count a * multiple r) :
    TensorObj.Restrict
      (kronFin k (fun r ↦ prescribedZPower T (b 2) grade (region r) (multiple r)))
      (prescribedZPower T (b 2) grade p m) := by sorry

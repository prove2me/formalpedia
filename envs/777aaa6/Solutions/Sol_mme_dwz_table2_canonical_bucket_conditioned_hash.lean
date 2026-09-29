-- Prove2me | solution 1 for mme_dwz_table2_canonical_bucket_conditioned_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:15:21.887444+00:00
-- url     : https://prove2.me/submissions/6a9c03d2-84d0-41c6-9cbf-bd3a8bf9b049

import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_dwz_same_affine_bucket_conditioned_XZ

open BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

/-- Two Table-2 words in one canonical first-hash bucket and one coarse-Z
fiber satisfy exactly Claim 6.8's conditioned X--Z hash equation. -/
theorem solution
    {p N : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (central candidate : Fin (N + 1) → Fin 15)
    (hcentral : central ∈ dwzTable2AffineHashBucket S A q)
    (hcandidate : candidate ∈ dwzTable2AffineHashBucket S A q)
    (hSameZ : ∀ t,
      DWZSquare.shapeZ (candidate t) = DWZSquare.shapeZ (central t)) :
    let weight : Fin (N + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let b0 : ZMod p := q.1 (Fin.last (N + 1))
    let hX : (Fin (N + 1) → ZMod p) →
        (Fin (N + 1) → ZMod p) → ZMod p := fun w I ↦
      b0 + ∑ t, I t * w t
    let hZ : ZMod p → (Fin (N + 1) → ZMod p) →
        (Fin (N + 1) → ZMod p) → ZMod p := fun w0 w K ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, ((4 : ZMod p) - K t) * w t)
    let conditionedW0 : (Fin (N + 1) → ZMod p) → ZMod p := fun w ↦
      2 * (∑ t, dwzTable2CastX central t * w t) -
        ∑ t, ((4 : ZMod p) - dwzTable2CastZ central t) * w t
    hX weight (dwzTable2CastX candidate) =
      hZ (conditionedW0 weight) weight (dwzTable2CastZ central) := by
  classical
  have hcentral' := (Finset.mem_filter.mp hcentral).2
  have hcandidate' := (Finset.mem_filter.mp hcandidate).2
  have hcastZ :
      dwzTable2CastZ (p := p) candidate =
        dwzTable2CastZ (p := p) central := by
    funext t
    exact congrArg (fun z : Fin 5 ↦ (z.val : ZMod p)) (hSameZ t)
  rw [hcastZ] at hcandidate'
  have hsupport (w : Fin (N + 1) → Fin 15) (t : Fin (N + 1)) :
      dwzTable2CastX (p := p) w t + dwzTable2CastY w t +
          dwzTable2CastZ w t =
        (4 : ZMod p) := by
    have hsum := DWZSquare.shape_sum (w t)
    have hcast := congrArg (fun n : ℕ ↦ (n : ZMod p)) hsum
    simpa only [dwzTable2CastX, dwzTable2CastY, dwzTable2CastZ,
      Nat.cast_add, Nat.cast_ofNat] using hcast
  have hsupportCandidate : ∀ t,
      dwzTable2CastX (p := p) candidate t +
          dwzTable2CastY candidate t + dwzTable2CastZ central t =
        (4 : ZMod p) := by
    intro t
    rw [← congrFun hcastZ t]
    exact hsupport candidate t
  exact mme_dwz_same_affine_bucket_conditioned_XZ
    hpodd S hSrange hSfree (4 : ZMod p)
      (dwzTable2CastX central) (dwzTable2CastY central)
      (dwzTable2CastZ central) (dwzTable2CastX candidate)
      (dwzTable2CastY candidate) (hsupport central)
      hsupportCandidate q hcentral' hcandidate'

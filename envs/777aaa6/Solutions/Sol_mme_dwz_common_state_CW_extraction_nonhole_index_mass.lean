-- Prove2me | solution 1 for mme_dwz_common_state_CW_extraction_nonhole_index_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T15:40:51.515074+00:00
-- url     : https://prove2.me/submissions/d77df755-6bc2-42bd-b982-40d4429a6baf

import Theorems.Thm_mme_dwz_selected_owner_nonhole_mass_and_disjointness
import Mathlib.Data.Fintype.EquivFin
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_dwz_useful_Z_boundary_filters_redundant
import Definitions.Def_mme_dwz_selected_owner_nonhole_data
import Theorems.Thm_mme_dwz_same_state_boundary_owned_CW_power_restrict

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.DWZStep1Support
open MME.DWZSimultaneous MME.DWZOwnerMass
universe u v w
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZCommonState

/-- Enumerating the selected targets does not require a separate good hash
state. Ambient isolation from the count is precisely what the actual CW
restriction uses, provided the ambient family represents every supported
same-marginal completion. -/
theorem selected_family_restrict
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N H p R k : ℕ)
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (hshape : ∀ c, shape c 0 + shape c 1 + shape c 2 = 2 * 2 ^ (ell - 1))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N,
      Supported (2 * 2 ^ (ell - 1)) a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (events : Fin R → Finset ((Fin (H + 2) → ZMod p) × ZMod p))
    (hevents : ∀ a state, state ∈ events a ↔
      Retained (2 * 2 ^ (ell - 1)) reindex S state (owner component shape a))
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (enumerate : Fin k ≃ ↥(selected targets ambient events
      (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state))
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦
        (source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
          (fun i w ↦ Allowed (fun j t ↦ component (enumerate j).val t)
            shape tag mu j i (label q ell N w))))
      (source K q ell N) := by
  classical
  let chosen : Fin k → Fin N → C := fun j t ↦ component (enumerate j).val t
  have hselected (j : Fin k) :
      (enumerate j).val ∈ targets ∧ state ∈ events (enumerate j).val ∧
      Isolated ambient events (fun a ↦ owner component shape a 0)
        (fun a ↦ owner component shape a 1) state (enumerate j).val := by
    exact Finset.mem_filter.mp (enumerate j).property
  refine mme_dwz_same_state_boundary_owned_CW_power_restrict
    q ell N H p k chosen shape hshape ?_ marginal ?_ reindex S hSrange hSfree hpodd
    state ?_ ?_ tag flip hflip htag mu hmuX hmuY
  · intro a b hab
    apply enumerate.injective
    apply Subtype.ext
    have hxy : owner component shape (enumerate a).val 0 =
        owner component shape (enumerate b).val 0 := congrArg (fun z ↦ z 0) hab
    exact (hselected b).2.2 (enumerate a).val (hsub (hselected a).1)
      (hselected a).2.1 (Or.inl hxy)
  · intro j
    exact hmarginal _ (hselected j).1
  · intro j
    exact (hevents _ state).mp (hselected j).2.1
  · intro j a ha hm hr hxy
    obtain ⟨b, hb, hba⟩ := hcomplete a ha hm
    have hret : state ∈ events b := (hevents b state).mpr (by simpa only [hba] using hr)
    have hxy' : owner component shape b 0 = owner component shape (enumerate j).val 0 ∨
        owner component shape b 1 = owner component shape (enumerate j).val 1 := by
      rw [hba]
      exact hxy.imp Eq.symm Eq.symm
    have heq : b = (enumerate j).val := (hselected j).2.2 b hb hret hxy'
    exact hba.symm.trans (congrArg (owner component shape) heq)

end MME.DWZCommonState


namespace MME.DWZCommonState

/-- The selected-family extraction with redundant boundary X/Y filters removed.
The selected set, enumeration, useful Z table, and unique-owner mask all remain
those of the same specified hash state. -/
theorem selected_family_padded_restrict
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N H p R k : ℕ)
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (hshape : ∀ c, shape c 0 + shape c 1 + shape c 2 = 2 * 2 ^ (ell - 1))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N,
      Supported (2 * 2 ^ (ell - 1)) a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (events : Fin R → Finset ((Fin (H + 2) → ZMod p) × ZMod p))
    (hevents : ∀ a state, state ∈ events a ↔
      Retained (2 * 2 ^ (ell - 1)) reindex S state (owner component shape a))
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (enumerate : Fin k ≃ ↥(selected targets ambient events
      (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state))
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦
        (source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
          (fun i w ↦
            Graded (fun j t ↦ component (enumerate j).val t)
              shape j i (label q ell N w) ∧
            (i = 2 → Profile (fun j t ↦ component (enumerate j).val t)
              tag mu j 2 (label q ell N w)) ∧
            (i = 2 → ∀ j',
              ZCompatible (fun j t ↦ component (enumerate j).val t)
                shape tag mu j' (label q ell N w) → j' = j))))
      (source K q ell N) := by
  apply TensorObj.Restrict.trans (mme_bigAdd_mono_restrict (fun j ↦
    mme_dwz_useful_Z_boundary_filters_redundant (K := K) q ell N k
      (fun j t ↦ component (enumerate j).val t) shape tag flip hflip htag
      mu hmuX hmuY j))
  exact selected_family_restrict (K := K) q ell N H p R k component shape
    hshape marginal targets ambient hsub hmarginal hcomplete reindex S
    hSrange hSfree hpodd events hevents state enumerate tag flip hflip htag
    mu hmuX hmuY

end MME.DWZCommonState


namespace MME.DWZCommonState

theorem enumerated_nonhole_iff_padded_Z
    {C : Type v} {W : Type w} {Block : Type*}
    [DecidableEq C] [DecidableEq W] [Fintype Block] [DecidableEq Block]
    {ell N R k : ℕ}
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (owners : Finset (Fin R)) (enumerate : Fin k ≃ ↥owners)
    (embed : Fin R → Block → FineWord ell N)
    (huseful : ∀ a ∈ owners, ∀ z,
      Graded component shape a 2 (embed a z) ∧ Profile component tag mu a 2 (embed a z))
    (j : Fin k) (z : Block) :
    z ∈ nonholes owners embed (fun f b ↦ ZCompatible component shape tag mu b f)
      (enumerate j).val ↔
      Graded (fun j t ↦ component (enumerate j).val t) shape j 2 (embed (enumerate j).val z) ∧
      Profile (fun j t ↦ component (enumerate j).val t) tag mu j 2 (embed (enumerate j).val z) ∧
      ∀ j', ZCompatible (fun j t ↦ component (enumerate j).val t)
        shape tag mu j' (embed (enumerate j).val z) → j' = j := by
  classical
  have hu := huseful (enumerate j).val (enumerate j).property z
  constructor
  · intro hn
    simp only [nonholes, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    refine ⟨hu.1, hu.2, ?_⟩
    intro j' hc
    apply enumerate.injective
    apply Subtype.ext
    exact hn (enumerate j').val (enumerate j').property hc
  · intro hn
    simp only [nonholes, Finset.mem_filter, Finset.mem_univ, true_and]
    intro b hb hc
    let ib : Fin k := enumerate.symm ⟨b, hb⟩
    have hc' : ZCompatible (fun j t ↦ component (enumerate j).val t)
        shape tag mu ib (embed (enumerate j).val z) := by
      change ZCompatible component shape tag mu (enumerate ib).val _ 
      simpa only [ib, Equiv.apply_symm_apply] using hc
    have heq : ib = j := hn.2.2 ib hc'
    have hv := congrArg (fun i ↦ (enumerate i).val) heq
    simpa only [ib, Equiv.apply_symm_apply] using hv

end MME.DWZCommonState

open MME.DWZCommonState

theorem solution
    {K : Type u} [Field K] {C : Type v} {W : Type w} {Block : Type*}
    [DecidableEq C] [DecidableEq W] [Fintype Block] [DecidableEq Block]
    (q ell N H p R : ℕ) [NeZero p]
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (hshape : ∀ c, shape c 0 + shape c 1 + shape c 2 = 2 * 2 ^ (ell - 1))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N,
      Supported (2 * 2 ^ (ell - 1)) a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (events : Fin R → Finset ((Fin (H + 2) → ZMod p) × ZMod p))
    (hevents : ∀ a state, state ∈ events a ↔
      Retained (2 * 2 ^ (ell - 1)) reindex S state (owner component shape a))
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w))
    (embed : Fin R → Block → FineWord ell N)
    (huseful : ∀ a ∈ targets, ∀ z,
      Graded component shape a 2 (embed a z) ∧ Profile component tag mu a 2 (embed a z))
    (K0 J d c : ℕ) (hK : K0 = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K0)
    (hx : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 0 = owner component shape a 0)).card ≤ d)
    (hy : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 1 = owner component shape a 1)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z,
      (competitors targets embed (fun f b ↦ ZCompatible component shape tag mu b f) a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient,
      b ≠ a → (owner component shape b 0 = owner component shape a 0 ∨
        owner component shape b 1 = owner component shape a 1) →
      (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z,
      ∀ b ∈ competitors targets embed (fun f b ↦ ZCompatible component shape tag mu b f) a z,
      (events a ∩ events b).card ≤ J) :
    ∃ state : (Fin (H + 2) → ZMod p) × ZMod p, ∃ k : ℕ,
      ∃ enumerate : Fin k ≃ ↥(selected targets ambient events
        (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j : Fin k ↦
          (source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
            (fun i w ↦
              Graded (fun j t ↦ component (enumerate j).val t)
                shape j i (label q ell N w) ∧
              (i = 2 → Profile (fun j t ↦ component (enumerate j).val t)
                tag mu j 2 (label q ell N w)) ∧
              (i = 2 → ∀ j',
                ZCompatible (fun j t ↦ component (enumerate j).val t)
                  shape tag mu j' (label q ell N w) → j' = j))))
        (source K q ell N) ∧
      (∀ j : Fin k, ∀ z : Block,
        z ∈ nonholes
          (selected targets ambient events
            (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state)
          embed (fun f b ↦ ZCompatible component shape tag mu b f) (enumerate j).val ↔
        Graded (fun j t ↦ component (enumerate j).val t)
          shape j 2 (embed (enumerate j).val z) ∧
        Profile (fun j t ↦ component (enumerate j).val t)
          tag mu j 2 (embed (enumerate j).val z) ∧
        ∀ j', ZCompatible (fun j t ↦ component (enumerate j).val t)
          shape tag mu j' (embed (enumerate j).val z) → j' = j) ∧
      3 * (targets.card * Fintype.card Block * K0) ≤
        8 * (Fintype.card ((Fin (H + 2) → ZMod p) × ZMod p) *
          ∑ a ∈ selected targets ambient events
            (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state,
            (nonholes
              (selected targets ambient events
                (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state)
              embed (fun f b ↦ ZCompatible component shape tag mu b f) a).card) := by
  classical
  have hself : ∀ a ∈ targets, ∀ z,
      ZCompatible component shape tag mu a (embed a z) := by
    intro a ha z
    refine ⟨(huseful a ha z).1, ?_⟩
    intro cell _ w
    exact (huseful a ha z).2 cell w
  obtain ⟨state, _, _, hmass⟩ := mme_dwz_selected_owner_nonhole_mass_and_disjointness
    targets ambient events
    (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1)
    embed (fun f b ↦ ZCompatible component shape tag mu b f)
    hsub hself K0 J p d c hK hxyBudget hzBudget hsingle hx hy hzCard hxyPair hzPair
  let owners := selected targets ambient events
    (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state
  let k := Fintype.card ↥owners
  let enumerate : Fin k ≃ ↥owners := (Fintype.equivFin ↥owners).symm
  refine ⟨state, k, enumerate, ?_, ?_, hmass⟩
  · exact selected_family_padded_restrict (K := K) q ell N H p R k component shape
      hshape marginal targets ambient hsub hmarginal hcomplete reindex S
      hSrange hSfree hpodd events hevents state enumerate tag flip hflip htag
      mu hmuX hmuY
  · intro j z
    apply enumerated_nonhole_iff_padded_Z component shape tag mu owners enumerate embed
    intro a ha u
    exact huseful a (Finset.mem_filter.mp ha).1 u



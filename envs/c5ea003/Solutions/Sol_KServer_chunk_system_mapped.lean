-- Prove2me | solution 1 for KServer.chunk_system_mapped
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T14:31:24.436494+00:00
-- url     : https://prove2.me/submissions/bc60d9b7-2aa1-444d-a426-ca66000a09c4

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer

namespace MapSys

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

open Classical in
/-- A canonical offline serving path: step into each nonempty request. -/
noncomputable def defaultPath (x₀ : X) (σ : List (Set X)) : ℕ → X
  | 0 => x₀
  | (j + 1) => if h : (σ.getD j ∅).Nonempty then h.choose else defaultPath x₀ σ j

theorem defaultPath_serves (x₀ : X) (σ : List (Set X)) :
    EvaderServes x₀ σ (defaultPath x₀ σ) := by
  refine ⟨rfl, ?_⟩
  intro j hne
  have hget : σ.get j = σ.getD (j : ℕ) ∅ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
    rfl
  show defaultPath x₀ σ ((j : ℕ) + 1) ∈ σ.get j
  rw [hget] at hne ⊢
  unfold defaultPath
  rw [dif_pos hne]
  exact hne.choose_spec

/-- The offline cost set is nonempty. -/
theorem offlineSet_nonempty (x₀ : X) (σ : List (Set X)) :
    {c : ℝ | ∃ P : ℕ → X, EvaderServes x₀ σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))}.Nonempty :=
  ⟨_, defaultPath x₀ σ, defaultPath_serves x₀ σ, rfl⟩

theorem offlineSet_bddBelow (x₀ : X) (σ : List (Set X)) :
    BddBelow {c : ℝ | ∃ P : ℕ → X, EvaderServes x₀ σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))} := by
  refine ⟨0, fun c hc => ?_⟩
  obtain ⟨P, -, hc⟩ := hc
  rw [hc]
  exact Finset.sum_nonneg fun j _ => dist_nonneg

/-- Offline costs do not increase along a request transformation admitting a
distance-preserving lift. -/
theorem offline_map_le (G : Set X → Set Y) (ι : X → Y)
    (hι : ∀ x x' : X, dist (ι x) (ι x') = dist x x')
    (hGsup : ∀ S : Set X, ι '' S ⊆ G S)
    (hGe : ∀ S : Set X, (G S).Nonempty → S.Nonempty)
    (x₀ : X) (σ : List (Set X)) :
    evaderOfflineCost (ι x₀) (reqMap G σ) ≤ evaderOfflineCost x₀ σ := by
  unfold evaderOfflineCost
  refine le_csInf (offlineSet_nonempty x₀ σ) ?_
  rintro c ⟨P, ⟨hP0, hPs⟩, hc⟩
  refine csInf_le (offlineSet_bddBelow _ _) ?_
  refine ⟨fun j => ι (P j), ⟨by show ι (P 0) = ι x₀; rw [hP0], ?_⟩, ?_⟩
  · intro j hne
    have hjl : (j : ℕ) < σ.length := by
      have h0 := j.isLt
      have hlen : (reqMap G σ).length = σ.length := reqMap_length G σ
      omega
    have hget : (reqMap G σ).get j = G (σ.get ⟨(j : ℕ), hjl⟩) := by
      show (reqMap G σ)[(j : ℕ)] = _
      unfold reqMap
      rw [List.getElem_map]
      rfl
    rw [hget] at hne ⊢
    have hSne : (σ.get ⟨(j : ℕ), hjl⟩).Nonempty := hGe _ hne
    have hmem := hPs ⟨(j : ℕ), hjl⟩ hSne
    exact hGsup _ ⟨P ((j : ℕ) + 1), hmem, rfl⟩
  · rw [hc, reqMap_length]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hι]

open Classical in
/-- **Mapped chunk systems**: a chunk system on `X` transforms into one on a
larger space `Y` along a request transformation `G` that is dominated by a
nonexpansive projection `π` and contains a distance-preserving lift `ι`.
Sample space, filtration, sizes — and hence the initial-history and
variance side conditions — are unchanged. -/
theorem chunk_system_map {s t : X} {a b : Y} {cA cB T pe pe' : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cA cB T pe mL)
    (G : Set X → Set Y) (π : Y → X) (ι : X → Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (hGe : ∀ S : Set X, (G S).Nonempty → S.Nonempty)
    (hι : ∀ x x' : X, dist (ι x) (ι x') = dist x x')
    (hGsup : ∀ S : Set X, ι '' S ⊆ G S)
    (hιs : ι s = a)
    (hab : dist s t ≤ dist a b)
    (hlastG : G {t} = {b})
    (hpe : pe ≤ pe')
    {V : ℝ}
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ C' : ChunkSystemB Y a b cA cB T pe' mL,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) := by
  refine ⟨{
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := C.m
    hist := C.hist
    chunk := fun ω i => reqMap G (C.chunk ω i)
    size := C.size
    hP := C.hP
    hPsum := C.hPsum
    hm := C.hm
    hm0 := C.hm0
    href := C.href
    hadapt := fun i ω ω' hh => by rw [C.hadapt i ω ω' hh]
    hsmeas := C.hsmeas
    hne := ?_
    hlast := ?_
    hopt := ?_
    hsize := C.hsize
    hcost := ?_
    htotal := C.htotal }, h0triv, hVar⟩
  · intro ω i S hS
    unfold reqMap at hS
    rw [List.mem_map] at hS
    obtain ⟨S₀, hS₀, rfl⟩ := hS
    exact hGne S₀ (C.hne ω i S₀ hS₀)
  · intro ω
    have h1 : (List.ofFn (fun i => reqMap G (C.chunk ω i))).flatten
        = reqMap G ((List.ofFn (C.chunk ω)).flatten) := by
      rw [reqMap_flatten, List.map_ofFn]
      rfl
    rw [h1]
    have h2 := C.hlast ω
    unfold reqMap
    rw [List.getLast?_map, h2]
    show some (G {t}) = _
    rw [hlastG]
  · intro ω
    have h1 : (List.ofFn (fun i => reqMap G (C.chunk ω i))).flatten
        = reqMap G ((List.ofFn (C.chunk ω)).flatten) := by
      rw [reqMap_flatten, List.map_ofFn]
      rfl
    rw [h1, ← hιs]
    refine le_trans (offline_map_le G ι hι hGsup hGe s _) ?_
    refine le_trans (C.hopt ω) ?_
    rw [hιs]
    exact hab
  · intro i ω₀ E bail
    have hshadow := fun ω =>
      shadow_bailCost_le π G hπ hG hGne E bail [] (((List.ofFn (C.chunk ω)).take i).flatten)
        (C.chunk ω i) hpe
    have hprem := C.hcost i ω₀
      (shadowEvader π G hG hGne E []) (fun l => bail ([] ++ reqMap G l))
    refine le_trans hprem ?_
    refine Finset.sum_le_sum fun ω hm => ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (C.hP ω))
    have h1 := hshadow ω
    have h2 : ([] : List (Set Y)) ++ reqMap G (((List.ofFn (C.chunk ω)).take i).flatten)
        = ((List.ofFn (fun j => reqMap G (C.chunk ω j))).take i).flatten := by
      rw [List.nil_append, reqMap_flatten]
      congr 1
      rw [List.map_take, List.map_ofFn]
      rfl
    rw [h2] at h1
    exact h1

end MapSys

namespace KServer

open MapSys in
/-- Mapped chunk systems along a projected request transformation. -/
theorem chunk_system_mapped {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s t : X} {a b : Y} {cA cB T pe pe' : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cA cB T pe mL)
    (G : Set X → Set Y) (π : Y → X) (ι : X → Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (hGe : ∀ S : Set X, (G S).Nonempty → S.Nonempty)
    (hι : ∀ x x' : X, dist (ι x) (ι x') = dist x x')
    (hGsup : ∀ S : Set X, ι '' S ⊆ G S)
    (hιs : ι s = a)
    (hab : dist s t ≤ dist a b)
    (hlastG : G {t} = {b})
    (hpe : pe ≤ pe')
    {V : ℝ}
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ C' : ChunkSystemB Y a b cA cB T pe' mL,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) :=
  chunk_system_map C G π ι hπ hG hGne hGe hι hGsup hιs hab hlastG hpe h0triv hVar

end KServer

theorem solution {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s t : X} {a b : Y} {cA cB T pe pe' : ℝ} {mL : ℕ}
    (C : KServer.ChunkSystemB X s t cA cB T pe mL)
    (G : Set X → Set Y) (π : Y → X) (ι : X → Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (hGe : ∀ S : Set X, (G S).Nonempty → S.Nonempty)
    (hι : ∀ x x' : X, dist (ι x) (ι x') = dist x x')
    (hGsup : ∀ S : Set X, ι '' S ⊆ G S)
    (hιs : ι s = a)
    (hab : dist s t ≤ dist a b)
    (hlastG : G {t} = {b})
    (hpe : pe ≤ pe')
    {V : ℝ}
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ C' : KServer.ChunkSystemB Y a b cA cB T pe' mL,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) :=
  KServer.chunk_system_mapped C G π ι hπ hG hGne hGe hι hGsup hιs hab hlastG hpe
    h0triv hVar

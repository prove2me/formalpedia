-- Prove2me | Definitions.Def_KServer_work_function
-- name    : KServer_work_function
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-31T13:43:43.9392+00:00
-- url     : https://prove2.me/theorems/5e89c8fd-f74e-41be-ad04-28ae6fb1f53d
-- title:
--   The work function and the Work Function Algorithm
-- statement:
--   The **work function** $w_{C_0,\sigma}(C)$ is the optimal cost of serving the request sequence $\sigma$ from the initial configuration $C_0$ and subsequently ending in the configuration $C$: the infimum over all serving schedules of (total movement cost) + (cost of the final move to $C$). On a **finite** metric space with $k \ge 1$ servers, the **Work Function Algorithm** is the deterministic online algorithm that, after each request $r$, moves to a configuration containing $r$ minimizing (movement cost from the current configuration) + (work function of the history including $r$); a minimizer exists by finiteness (proved, not assumed), and ties are broken by a fixed arbitrary choice, matching the standard definition's "ties broken arbitrarily". The file proves the service property, so `WFA` is a bona fide `OnlineAlgorithm` with `conf [] = C₀`.
-- source:
--   E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5), 1995 (the work function algorithm); C. Coester, E. Koutsoupias, Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle, ICALP 2021, https://arxiv.org/abs/2102.10474, Section 2 (WFA selects $C_t \ni r_t$ minimizing $d(C_{t-1},C_t)+w_t(C_t)$, ties broken arbitrarily)

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

variable {k : ℕ} {M : Type*} [MetricSpace M]

/-- The **work function**: `workFunction C₀ σ C` is the optimal cost of serving
the request sequence `σ` starting from the configuration `C₀` and subsequently
ending in the configuration `C` — the infimum, over all schedules `S` serving
`σ` from `C₀`, of the schedule's total movement cost plus the cost of moving
from the schedule's final configuration to `C`. -/
noncomputable def workFunction (C₀ : Config k M) (σ : List M) (C : Config k M) : ℝ :=
  sInf {t : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    t = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))) + moveCost (S σ.length) C}

section Finite

variable [Fintype M]

/-- On a finite metric space with at least one server, among the configurations
containing the new request `r` there is one minimizing (movement cost from the
previous configuration) + (work function after the request). -/
lemma exists_wfa_min (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) :
    ∃ C : Config k M, (∃ i, C i = r) ∧
      ∀ C' : Config k M, (∃ i, C' i = r) →
        moveCost Cprev C + workFunction C₀ (l ++ [r]) C ≤
          moveCost Cprev C' + workFunction C₀ (l ++ [r]) C' := by
  classical
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun C : Config k M => ∃ i, C i = r)
    (fun C => moveCost Cprev C + workFunction C₀ (l ++ [r]) C)
    ⟨Function.update Cprev ⟨0, hk⟩ r,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨0, hk⟩, by simp⟩⟩⟩
  exact ⟨C, (Finset.mem_filter.mp hC).2,
    fun C' hC' => hmin C' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'⟩)⟩

/-- One step of the **Work Function Algorithm**: after the request history `l`,
in configuration `Cprev`, on the new request `r`, move to a configuration
containing `r` that minimizes (movement cost from `Cprev`) + (work function of
the extended history `l ++ [r]`). A minimizer exists by `exists_wfa_min`; ties
are broken by a fixed arbitrary choice. -/
noncomputable def wfaStep (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) : Config k M :=
  (exists_wfa_min hk C₀ l Cprev r).choose

lemma wfaStep_serves (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) : ∃ i, wfaStep hk C₀ l Cprev r i = r :=
  (exists_wfa_min hk C₀ l Cprev r).choose_spec.1

lemma wfaStep_min (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) :
    ∀ C' : Config k M, (∃ i, C' i = r) →
      moveCost Cprev (wfaStep hk C₀ l Cprev r) +
        workFunction C₀ (l ++ [r]) (wfaStep hk C₀ l Cprev r) ≤
      moveCost Cprev C' + workFunction C₀ (l ++ [r]) C' :=
  (exists_wfa_min hk C₀ l Cprev r).choose_spec.2

/-- Auxiliary fold computing, along a request list, the pair
(request history processed so far, current WFA configuration). -/
noncomputable def wfaAux (hk : 0 < k) (C₀ : Config k M) (l : List M) :
    List M × Config k M :=
  l.foldl (fun p r => (p.1 ++ [r], wfaStep hk C₀ p.1 p.2 r)) ([], C₀)

private lemma wfaAux_foldl_fst (hk : 0 < k) (C₀ : Config k M) (l : List M) :
    ∀ p : List M × Config k M,
      (l.foldl (fun q r => (q.1 ++ [r], wfaStep hk C₀ q.1 q.2 r)) p).1 = p.1 ++ l := by
  induction l with
  | nil => intro p; simp
  | cons r t ih => intro p; simp [List.foldl_cons, ih, List.append_assoc]

@[simp] lemma wfaAux_fst (hk : 0 < k) (C₀ : Config k M) (l : List M) :
    (wfaAux hk C₀ l).1 = l := by
  simpa [wfaAux] using wfaAux_foldl_fst hk C₀ l ([], C₀)

lemma wfaAux_append (hk : 0 < k) (C₀ : Config k M) (l : List M) (r : M) :
    wfaAux hk C₀ (l ++ [r]) =
      ((wfaAux hk C₀ l).1 ++ [r],
        wfaStep hk C₀ (wfaAux hk C₀ l).1 (wfaAux hk C₀ l).2 r) := by
  unfold wfaAux
  rw [List.foldl_append]
  rfl

/-- **The Work Function Algorithm** on a finite metric space, from the initial
configuration `C₀` (with `k ≥ 1` servers), as a deterministic online
algorithm: after each request it moves to a configuration containing the
request minimizing (movement cost) + (work function of the history including
the request), ties broken by a fixed arbitrary choice. -/
noncomputable def WFA (hk : 0 < k) (C₀ : Config k M) : OnlineAlgorithm k M where
  conf l := (wfaAux hk C₀ l).2
  serves l r := by
    have h := wfaStep_serves hk C₀ (wfaAux hk C₀ l).1 (wfaAux hk C₀ l).2 r
    simpa [wfaAux_append hk C₀ l r] using h

@[simp] lemma WFA_conf_nil (hk : 0 < k) (C₀ : Config k M) :
    (WFA hk C₀).conf [] = C₀ := rfl

end Finite

end KServer



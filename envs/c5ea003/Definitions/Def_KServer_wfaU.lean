-- Prove2me | Definitions.Def_KServer_wfaU
-- name    : KServer_wfaU
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T03:57:33.20742+00:00
-- url     : https://prove2.me/theorems/dfc900b0-e2df-450b-9ada-6b73be152045
-- title:
--   The classical Work Function Algorithm (unlabelled work function)
-- statement:
--   The **Work Function Algorithm** of Chrobak--Larmore and Koutsoupias--Papadimitriou, in its classical form.
--
--   After each request $r$, from its current configuration $A$ and with request history $l$, the algorithm moves to a configuration $X$ containing $r$ that minimises
--
--   $$d(A, X) \;+\; w_{l r}(X),$$
--
--   where $w$ is the work function of the **unlabelled** configuration --- the one whose final move is a minimum-cost matching rather than a move of individually named servers. This is the algorithm all the classical analyses are about: the $(2k-1)$-competitiveness of Koutsoupias and Papadimitriou, the $k$-competitiveness results on special spaces, and the $3$-competitiveness for three servers on trees of Coester and Koutsoupias.
--
--   ## Why the unlabelled work function
--
--   A configuration is presented here as a function $\{1,\dots,k\} \to M$, so it carries a labelling, and the movement cost $d(A,X) = \sum_i d(A_i, X_i)$ charges each named server for its own travel. The work function built on that convention --- which demands that server $i$ finish at $X_i$ --- is *not* the classical one, and an algorithm built from it is not the classical Work Function Algorithm: already for $k=2$ and an empty request history it separates a configuration from its own transposition by twice a distance.
--
--   Minimising $d(A,X) + w(X)$ over *labelled* configurations $X$, with $w$ the unlabelled work function, resolves this without any extra bookkeeping. Since $w$ is invariant under relabelling its argument while $d(A, \cdot)$ is not, the minimisation automatically selects a labelling of the chosen point multiset realising the minimum-cost matching from $A$. The algorithm therefore moves its servers along an optimal matching, which is what the classical description prescribes, and its cost --- measured with the labelled movement cost --- is the cost of that matching.
--
--   ## Contents
--
--   `exists_wfaU_min` provides the minimiser, on a finite metric space, among the configurations covering the request; `wfaUStep` is one step of the algorithm, with `wfaUStep_serves` and `wfaUStep_min` recording its two defining properties; `wfaUAux` folds the step along a request list; and `WFAU` packages the result as a deterministic online algorithm, with `WFAU_conf_nil` identifying its initial configuration. Ties in the minimisation are broken by a fixed arbitrary choice.
-- source:
--   M. Chrobak, L. Larmore, 'The server problem and on-line games', 1991; E. Koutsoupias, C. H. Papadimitriou, 'On the k-server conjecture', JACM 42 (1995), Section 2; E. Koutsoupias, 'The k-server problem', Computer Science Review 3 (2009), Section 3; C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Preliminaries — where WFA moves to a configuration X containing the request minimising d(A,X) + w(X) with w the work function on (unlabelled) configurations and d the minimum-cost matching distance.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

variable {k : ℕ} {M : Type*} [MetricSpace M]

section Finite

variable [Fintype M]

/-- On a finite metric space with at least one server, among the configurations
containing the new request `r` there is one minimizing (movement cost from the
previous configuration) + (the **unlabelled** work function after the request). -/
lemma exists_wfaU_min (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) :
    ∃ C : Config k M, (∃ i, C i = r) ∧
      ∀ C' : Config k M, (∃ i, C' i = r) →
        moveCost Cprev C + workFnU C₀ (l ++ [r]) C ≤
          moveCost Cprev C' + workFnU C₀ (l ++ [r]) C' := by
  classical
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun C : Config k M => ∃ i, C i = r)
    (fun C => moveCost Cprev C + workFnU C₀ (l ++ [r]) C)
    ⟨Function.update Cprev ⟨0, hk⟩ r,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨0, hk⟩, by simp⟩⟩⟩
  exact ⟨C, (Finset.mem_filter.mp hC).2,
    fun C' hC' => hmin C' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'⟩)⟩

/-- One step of the **classical Work Function Algorithm**: after the request
history `l`, in configuration `Cprev`, on the new request `r`, move to a
configuration containing `r` that minimizes (movement cost from `Cprev`) + (the
unlabelled work function of the extended history `l ++ [r]`). Because `workFnU`
does not depend on how its argument is labelled while `moveCost` does, the
minimization automatically selects a labelling realizing the minimum-cost
matching, so the algorithm moves its servers along an optimal matching. -/
noncomputable def wfaUStep (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) : Config k M :=
  (exists_wfaU_min hk C₀ l Cprev r).choose

lemma wfaUStep_serves (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) : ∃ i, wfaUStep hk C₀ l Cprev r i = r :=
  (exists_wfaU_min hk C₀ l Cprev r).choose_spec.1

lemma wfaUStep_min (hk : 0 < k) (C₀ : Config k M) (l : List M)
    (Cprev : Config k M) (r : M) :
    ∀ C' : Config k M, (∃ i, C' i = r) →
      moveCost Cprev (wfaUStep hk C₀ l Cprev r) +
        workFnU C₀ (l ++ [r]) (wfaUStep hk C₀ l Cprev r) ≤
      moveCost Cprev C' + workFnU C₀ (l ++ [r]) C' :=
  (exists_wfaU_min hk C₀ l Cprev r).choose_spec.2

/-- Auxiliary fold computing, along a request list, the pair
(request history processed so far, current configuration). -/
noncomputable def wfaUAux (hk : 0 < k) (C₀ : Config k M) (l : List M) :
    List M × Config k M :=
  l.foldl (fun p r => (p.1 ++ [r], wfaUStep hk C₀ p.1 p.2 r)) ([], C₀)

private lemma wfaUAux_foldl_fst (hk : 0 < k) (C₀ : Config k M) (l : List M) :
    ∀ p : List M × Config k M,
      (l.foldl (fun q r => (q.1 ++ [r], wfaUStep hk C₀ q.1 q.2 r)) p).1 = p.1 ++ l := by
  induction l with
  | nil => intro p; simp
  | cons r t ih => intro p; simp [List.foldl_cons, ih, List.append_assoc]

@[simp] lemma wfaUAux_fst (hk : 0 < k) (C₀ : Config k M) (l : List M) :
    (wfaUAux hk C₀ l).1 = l := by
  simpa [wfaUAux] using wfaUAux_foldl_fst hk C₀ l ([], C₀)

lemma wfaUAux_append (hk : 0 < k) (C₀ : Config k M) (l : List M) (r : M) :
    wfaUAux hk C₀ (l ++ [r]) =
      ((wfaUAux hk C₀ l).1 ++ [r],
        wfaUStep hk C₀ (wfaUAux hk C₀ l).1 (wfaUAux hk C₀ l).2 r) := by
  unfold wfaUAux
  rw [List.foldl_append]
  rfl

/-- **The classical Work Function Algorithm** on a finite metric space, from the
initial configuration `C₀` (with `k ≥ 1` servers), as a deterministic online
algorithm. It is the algorithm of Chrobak–Larmore and Koutsoupias–Papadimitriou:
after each request it moves to a configuration containing the request minimizing
(movement cost) + (the work function of the unlabelled configuration), the work
function being the one whose final move is a minimum-cost matching. -/
noncomputable def WFAU (hk : 0 < k) (C₀ : Config k M) : OnlineAlgorithm k M where
  conf l := (wfaUAux hk C₀ l).2
  serves l r := by
    have h := wfaUStep_serves hk C₀ (wfaUAux hk C₀ l).1 (wfaUAux hk C₀ l).2 r
    simpa [wfaUAux_append hk C₀ l r] using h

@[simp] lemma WFAU_conf_nil (hk : 0 < k) (C₀ : Config k M) :
    (WFAU hk C₀).conf [] = C₀ := rfl

end Finite

end KServer


